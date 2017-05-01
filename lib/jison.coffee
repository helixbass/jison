# Jison, an LR(0), SLR(1), LARL(1), LR(1) Parser Generator
# Zachary Carter <zach@carter.name>
# MIT X Licensed

{typal}    = require './util/typal'
{Set}      = require './util/set'
Lexer      = require 'jison-lex'
ebnfParser = require 'ebnf-parser'
JSONSelect = require 'JSONSelect'
esprima    = require 'esprima'
escodegen  = require 'escodegen'


{version} = require '../package.json'

Jison = exports.Jison = exports
Jison.version = version

# detect print
Jison.print =
  if console?.log
    console.log
  else if puts?
    (args...) -> puts args.join ' '
  else if print?
    print
  else
    ->

Jison.Parser = do ->

  # iterator utility
  each = (obj, func) ->
    return obj.forEach func if obj.forEach

    func.call obj, obj[prop], prop, obj for own prop of obj

  isString = (obj) ->
    typeof obj is 'string'
  isArray = (obj) ->
    obj.constructor is Array
  isFunction = (obj) ->
    typeof obj is 'function'
  extend = (obj, objs...) ->
    typal.mix.call obj, objs...
  extended = (obj, objs...) ->
    typal.mix.call {}, obj, objs...
  toList = (listOrString, strClb) ->
    strClb ?= (str) -> str.trim().split ' '
    return strClb listOrString if isString listOrString

    listOrString[...]

  Nonterminal = typal.construct
    constructor: (@symbol) ->
      @productions = new Set
      @first = []
      @follows = []
      @nullable = no
    toString: ->
      """
      #{ @symbol }
      #{ unless @nullable then 'not ' else '' }nullable
      Firsts: #{ @first.join ', ' }
      Follows: #{ @follows.join ', ' }
      Productions:
        #{ @productions.join '\n  ' }
      """

  Production = typal.construct
    constructor: (@head, @body, @id, @precedence = 0) ->
      @nullable = no
      @first = []
    toString: ->
      "#{ @head } -> #{ @body.join ' ' }"

  generator = typal.beget
    constructor: (grammar, opt) ->
      grammar = ebnfParser.parse grammar if isString grammar
      {parseParams, actionInclude, moduleInclude, lex, options} = grammar
      extend options, opt
      {debug} = options
      extend @, {
        terms: {}
        conflicts: 0
        resolutions: []
        options, parseParams
        yy: {} # accessed as yy free variable in the parser/lexer actions
        # source included in semantic action execution scope
        actionInclude:
          if actionInclude
            if isFunction actionInclude
              String actionInclude
              .replace /^\s*function \(\) \{/, ''
              .replace /\}\s*$/, ''
            else
              actionInclude
          else ''
        moduleInclude: moduleInclude or ''
        DEBUG: debug or no
      }

      @mix generatorDebug if @DEBUG # mixin debug methods

      @processGrammar grammar

      @lexer = new Lexer lex, null, @terminals_ if lex

    # set precedence and associativity of operators
    processOperators: (ops) ->
      @operators = do =>
        return {} unless ops
        operators = {}
        for i, precLevel in ops
          [assoc, opsAtLevel...] = precLevel
          operators[op] = { assoc, precedence: i + 1 } for op in opsAtLevel
        operators

    processGrammar: (grammar) ->
      {bnf, tokens, ebnf, operators} = grammar
      bnf = grammar.bnf = ebnfParser.transform ebnf if ebnf and not bnf
      tokens = toList tokens if tokens

      @processOperators operators

      # build productions from cfg
      @buildProductions { bnf }

      if tokens and @terminals.length isnt tokens.length
        @trace "Warning: declared tokens differ from tokens found in rules."
        @trace @terminals
        @trace tokens

      @augmentGrammar grammar

    buildProductions: ({bnf}) ->
      actions = [
        '/* this == yyval */'
        @actionInclude
        'var $0 = $$.length - 1;'
        'switch (yystate) {'
      ]
      actionGroups = {}

      @hasErrorRecovery = no

      @symbols_ = {}
      @symbols = []
      # add error symbol; will be third symbol, or "2" ($accept, $end, error)
      @addSymbol 'error'

      @productions = []
      @productions_ = [0]
      @nonterminals = {}
      for own head, handles of bnf
        @addSymbol head
        @addNonterminal head

        @buildProduction { handle, head } for handle in toList handles, (str) -> str.split /\s*\|\s*/g

      for action, caseClauses of actionGroups
        actions.push caseClauses.join(' '), action, 'break;'

      @terminals = []
      @terminals_ = {}
      each @symbols_, (id, sym) =>
        return if @nonterminals[sym]

        @terminals.push sym
        @terminals_[id] = sym

      actions.push '}'

      actions =
        actions
        .join '\n'
        .replace /YYABORT/g, 'return false'
        .replace /YYACCEPT/g, 'return true'

      parameters = "
        yytext, yyleng, yylineno, yy, yystate /* action[1] */, $$ /* vstack */, _$ /* lstack */#{
          if @parseParams
            ", #{ @parseParams.join ', ' }"
          else ''
        }
        "

      @performAction = """
        function anonymous(#{ parameters }) {
        #{ actions }
        }"""

    addSymbol: (symbol) ->
      @_symbolId = 1 unless @symbols.length
      return unless symbol and not @symbols_[symbol]

      @symbols_[symbol] = ++@_symbolId
      @symbols.push symbol

    buildProduction: ({handle, head}) ->
      @addProduction {
        head
        production: do =>
          if isArray handle
            [body, action, opts] = handle
            body = toList body
            if isString action
              actionSpecified = yes
            else
              opts = action
          else
            body =
              @stripAliases handle
              .trim().split ' '

          for symbol in body
            @hasErrorRecovery = yes if symbol is 'error'
            @addSymbol symbol

          newProductionId = @productions.length + 1
          if actionSpecified
            action = @replaceActionVars { action, body }
            (actionGroups[action] ?= []).push "case #{ newProductionId }:"

          @setMissingPrecedence new Production(
            head
            body.map @stripAliases
            newProductionId
            @operators[opts.prec].precedence if opts and @operators[opts.prec]
          )
      }

    stripAliases: (symbol) ->
      symbol.replace ///
        \[
        [a-zA-Z_]
        [a-zA-Z0-9_-] *
        \]
      ///g, ''

    replaceActionVars: ({action, body}) ->
      # replace named semantic values ($nonterminal)
      if action.match /[$@][a-zA-Z][a-zA-Z0-9_]*/
        count = {}
        names = {}
        for bodyIndex, symbol in body
          # check for aliased names, e.g., id[alias]
          matchedAlias =
            symbol.match ///
              ^
              ( [^\[] * ) # base
              \[
              ( # alias
                [a-zA-Z]
                [a-zA-Z0-9_-] *
              )
              \]
            ///
          useSymbol =
            if matchedAlias
              [fullMatch, base, alias] = matchedAlias
              body[bodyIndex] = base
              alias
            else
              symbol
          count[useSymbol] ?= 0
          names["#{ useSymbol }#{ ++count[useSymbol]}"] = bodyIndex + 1
          names[useSymbol] ?= bodyIndex + 1

        action =
          action
          .replace ///
            \$
            (
              [a-zA-Z]
              [a-zA-Z0-9_] *
            )
          ///g, (fullMatch, name) ->
            if names[name]
              "$#{ names[name] }"
            else fullMatch
          .replace ///
            @
            (
              [a-zA-Z]
              [a-zA-Z0-9_] *
            )
          ///g, (fullMatch, name) ->
            if names[name]
              "@#{ names[name] }"
            else fullMatch
      action
      # replace references to $$ with this.$, and @$ with this._$
      .replace ///
        ( [^'"] )
        \$\$
        |
        ^ \$\$
      ///g, '$1this.$'
      .replace /@[0$]/g, "this._$"

      # replace semantic value references ($n) with stack value (stack[n])
      .replace ///
        \$
        (
          - ?
          \d +
        )
      ///g, (fullMatch, num) ->
        "$$[$0#{ num - body.length or '' }]"
      # same as above for location references (@n)
      .replace ///
        @
        (
          - ?
          \d +
        )
      ///g, (fullMatch, num) ->
        "_$[$0#{ num - body.length or '' }]"

    setMissingPrecedence: ( production ) ->
      {precedence, body} = production
      return production unless precedence is 0

      for symbol in body by -1
        if symbol not in @nonterminals and symbol in @operators
          production.precedence = @operators[symbol].precedence
      production

    addProduction: ({production, head}) ->
      @productions.push production
      @productions_.push [
        @symbols_[head]
        if production.body[0] is ''
          0
        else
          production.body.length
      ]
      @nonterminals[head].productions.push production

    augmentGrammar: ({start, startSymbol}) ->
      throw new Error 'Grammar error: must have at least one rule.' unless @productions.length
      # use specified start symbol, or default to first user defined production
      @startSymbol = start or startSymbol or @productions[0].head
      throw new Error 'Grammar error: startSymbol must be a non-terminal found in your grammar.' unless @nonterminals[@startSymbol]
      @EOF = '$end'

      # augment the grammar
      acceptProduction = new Production '$accept', [@startSymbol, '$end'], 0
      @productions.unshift acceptProduction

      # prepend parser tokens
      @symbols.unshift '$accept', @EOF
      @symbols_.$accept = 0
      @symbols_[@EOF] = 1
      @terminals.unshift @EOF

      @addNonterminal '$accept', (acceptNonterminal) ->
        acceptNonterminal.productions.push acceptProduction

      # add follow $ to start symbol
      @nonterminals[@startSymbol].follows.push @EOF

    addNonterminal: (symbol, clb) ->
      @nonterminals[symbol] = new Nonterminal symbol
      clb? @nonterminals[symbol]

    createParser: ->
      throw new Error 'Calling abstract method.'

    # noop. implemented in debug mixin
    trace: ->

    warn: (args...) ->
      Jison.print.call null, args.join ''

    error: (msg) ->
      throw new Error msg

  # Generator debug mixin

  generatorDebug =
    trace: ->
      Jison.print.apply null, arguments
    beforeprocessGrammar: ->
      @trace 'Processing grammar.'
    afteraugmentGrammar: ->
      each @symbols, (sym, i) ->
        @trace "#{ sym }(#{ i })"



  ###
  # Mixin for common behaviors of lookahead parsers
  ###
  lookaheadMixin =
    computeLookaheads: ->
      @mix lookaheadDebug if @DEBUG # mixin debug methods

      @computeLookaheads = ->
      do @nullableSets
      do @firstSets
      do @followSets

    # fixed-point calculation of NULLABLE
    nullableSets: ->
      @loopWhileChanged
        # check if each production is nullable
        productionClb: (production) =>
          {nullable, body} = production
          return if nullable

          return unless @nullable body

          production.nullable = yes

        # check if each symbol is nullable
        nonterminalClb: (nonterminal, symbol) =>
          return if @nullable symbol

          changed = no
          nonterminal.productions.forEach (production) ->
            nonterminal.nullable = changed = yes if production.nullable
          changed

    # check if a token or series of tokens is nullable
    nullable: (symbol) ->
      @computeSymbolProperty {
        ifEpsilon: -> yes
        ifBody: =>
          return no for sym in symbol when not @nullable sym
          yes
        ifTerminal: -> no
        ifNonterminal: ({nullable}) -> nullable
        symbol
      }

    # fixed-point calculation of FIRST sets
    firstSets: ->
      @loopWhileChanged
        productionClb: (production) =>
          {body, first} = production
          firsts = @first body
          return if firsts.length is first.length

          production.first = firsts

        nonterminalClb: (nonterminal, symbol) ->
          {productions, first} = nonterminal
          firsts = []
          productions.forEach (production) ->
            Set.union firsts, production.first
          return if firsts.length is first.length

          nonterminal.first = firsts

    # return the FIRST set of a symbol or series of symbols
    first: (symbol) ->
      @computeSymbolProperty {
        ifEpsilon: -> []
        ifBody: =>
          firsts = []
          for sym in symbol
            if nonterminal=@nonterminals[sym]
              Set.union firsts, nonterminal.first
            else
              firsts.push sym if firsts.indexOf(sym) is -1
            break unless @nullable sym
          firsts
        ifTerminal: -> [symbol]
        ifNonterminal: ({first}) -> first
        symbol
      }

    # calculate follow sets typald on first and nullable
    followSets: ->
      @loopWhileChanged
        productionClb: (production) =>
          {head, body} = production
          #@trace(production.head,@nonterminals[production.head].follows);
          # q is used in Simple LALR algorithm determine follows in context
          isSimpleLALR = !! @go_

          for i, symbol in body
            continue unless @nonterminals[symbol]

            # for Simple LALR algorithm, @go_ checks if
            q = @go_ head, body[0...i] if isSimpleLALR
            bool = not isSimpleLALR or q is parseInt @nterms_[symbol], 10

            if i is body.length + 1 and bool # TODO: how could i ever be that?
              set = @nonterminals[head].follows
            else
              part = body[i + 1..]

              set = @first part
              if @nullable(part) and bool
                set.push @nonterminals[head].follows...
            {follows} = @nonterminals[symbol]
            oldCount = follows.length
            Set.union follows, set
            oldCount isnt follows.length

    loopWhileChanged: ({productionClb, nonterminalClb}) ->
      changed = yes
      while changed
        changed = no

        if productionClb
          @productions.forEach (production) =>
            changed = yes if productionClb.call @, production

        if nonterminalClb
          @nonterminals.forEach (nonterminal, symbol) =>
            changed = yes if nonterminalClb.call @, nonterminal, symbol

    computeSymbolProperty: ({symbol, ifEpsilon, ifBody, ifTerminal, ifNonterminal}) ->
      return do ifEpsilon  if symbol is ''
      return do ifBody     if isArray symbol
      return do ifTerminal unless nonterminal=@nonterminals[symbol]
      ifNonterminal nonterminal


  # lookahead debug mixin
  lookaheadDebug =
    beforenullableSets: ->
      @trace 'Computing Nullable sets.'
    beforefirstSets: ->
      @trace 'Computing First sets.'
    beforefollowSets: ->
      @trace 'Computing Follow sets.'
    afterfollowSets: ->
      each @nonterminals, (nonterminal) =>
        @trace nonterminal, '\n'

  var NONASSOC = 0;
  lrGeneratorMixin.parseTable = function parseTable (itemSets) {
      var states = [],
          nonterminals = this.nonterminals,
          operators = this.operators,
          conflictedStates = {}, // array of [state, token] tuples
          self = this,
          s = 1, // shift
          r = 2, // reduce
          a = 3; // accept

      // for each item set
      itemSets.forEach(function (itemSet, k) {
          var state = states[k] = {};
          var action, stackSymbol;

          // set shift and goto actions
          for (stackSymbol in itemSet.edges) {
              itemSet.forEach(function (item, j) {
                  // find shift and goto actions
                  if (item.markedSymbol == stackSymbol) {
                      var gotoState = itemSet.edges[stackSymbol];
                      if (nonterminals[stackSymbol]) {
                          // store state to go to after a reduce
                          //self.trace(k, stackSymbol, 'g'+gotoState);
                          state[self.symbols_[stackSymbol]] = gotoState;
                      } else {
                          //self.trace(k, stackSymbol, 's'+gotoState);
                          state[self.symbols_[stackSymbol]] = [s,gotoState];
                      }
                  }
              });
          }

          // set accept action
          itemSet.forEach(function (item, j) {
              if (item.markedSymbol == self.EOF) {
                  // accept
                  state[self.symbols_[self.EOF]] = [a];
                  //self.trace(k, self.EOF, state[self.EOF]);
              }
          });

          var allterms = self.lookAheads ? false : self.terminals;

          // set reductions and resolve potential conflicts
          itemSet.reductions.forEach(function (item, j) {
              // if parser uses lookahead, only enumerate those terminals
              var terminals = allterms || self.lookAheads(itemSet, item);

              terminals.forEach(function (stackSymbol) {
                  action = state[self.symbols_[stackSymbol]];
                  var op = operators[stackSymbol];

                  // Reading a terminal and current position is at the end of a production, try to reduce
                  if (action || action && action.length) {
                      var sol = resolveConflict(item.production, op, [r,item.production.id], action[0] instanceof Array ? action[0] : action);
                      self.resolutions.push([k,stackSymbol,sol]);
                      if (sol.bydefault) {
                          self.conflicts++;
                          if (!self.DEBUG) {
                              self.warn('Conflict in grammar: multiple actions possible when lookahead token is ',stackSymbol,' in state ',k, "\n- ", printAction(sol.r, self), "\n- ", printAction(sol.s, self));
                              conflictedStates[k] = true;
                          }
                          if (self.options.noDefaultResolve) {
                              if (!(action[0] instanceof Array))
                                  action = [action];
                              action.push(sol.r);
                          }
                      } else {
                          action = sol.action;
                      }
                  } else {
                      action = [r,item.production.id];
                  }
                  if (action && action.length) {
                      state[self.symbols_[stackSymbol]] = action;
                  } else if (action === NONASSOC) {
                      state[self.symbols_[stackSymbol]] = undefined;
                  }
              });
          });

      });

      if (!self.DEBUG && self.conflicts > 0) {
          self.warn("\nStates with conflicts:");
          each(conflictedStates, function (val, state) {
              self.warn('State '+state);
              self.warn('  ',itemSets.item(state).join("\n  "));
          });
      }

      return states;
  };

  # find states with only one action, a reduction
  findDefaults  = (states) ->
    defaults = {}
    states.forEach (state, key) ->
      return unless [action for own action of state].length is 1
      loneAction = state[action]
      return unless loneAction[0] is 2

      # only one action in state and it's a reduction
      defaults[key] = loneAction

    defaults

  // resolves shift-reduce and reduce-reduce conflicts
  function resolveConflict (production, op, reduce, shift) {
      var sln = {production: production, operator: op, r: reduce, s: shift},
          s = 1, // shift
          r = 2, // reduce
          a = 3; // accept

      if (shift[0] === r) {
          sln.msg = "Resolve R/R conflict (use first production declared in grammar.)";
          sln.action = shift[1] < reduce[1] ? shift : reduce;
          if (shift[1] !== reduce[1]) sln.bydefault = true;
          return sln;
      }

      if (production.precedence === 0 || !op) {
          sln.msg = "Resolve S/R conflict (shift by default.)";
          sln.bydefault = true;
          sln.action = shift;
      } else if (production.precedence < op.precedence ) {
          sln.msg = "Resolve S/R conflict (shift for higher precedent operator.)";
          sln.action = shift;
      } else if (production.precedence === op.precedence) {
          if (op.assoc === "right" ) {
              sln.msg = "Resolve S/R conflict (shift for right associative operator.)";
              sln.action = shift;
          } else if (op.assoc === "left" ) {
              sln.msg = "Resolve S/R conflict (reduce for left associative operator.)";
              sln.action = reduce;
          } else if (op.assoc === "nonassoc" ) {
              sln.msg = "Resolve S/R conflict (no action for non-associative operator.)";
              sln.action = NONASSOC;
          }
      } else {
          sln.msg = "Resolve conflict (reduce for higher precedent production.)";
          sln.action = reduce;
      }

      return sln;
  }

  ###
  # Mixin for common LR parser behavior
  ###
  lrGeneratorMixin =
    buildTable: ->
      @mix lrGeneratorDebug if @DEBUG # mixin debug methods

      @states = do @canonicalCollection
      @table = @parseTable @states
      @defaultActions = findDefaults @table

    ###
    # Create unique set of item sets
    ###
    canonicalCollection: ->
      firstState =
        @closureOperation(
          new @ItemSet(
            new @Item @productions[0], 0, [@EOF]
          ))
      states = new Set firstState
      marked = 0

      states.has = {}
      states.has[firstState] = 0

      while marked isnt do states.size
        itemSet = states.item marked
        marked++
        for item of itemSet
          if item.markedSymbol and item.markedSymbol isnt @EOF
            @canonicalCollectionInsert item.markedSymbol, itemSet, states, marked - 1

      states

    Item: typal.construct
      constructor: (@production, @dotPosition=0, @follows=[], @predecessor) ->
        @id = parseInt "#{ production.id }a#{ @dotPosition }", 36
        @markedSymbol = @production.body[@dotPosition]
      remainingHandle: ->
        @production.body[@dotPosition + 1..]
      eq: ({id}) ->
        id is @id
      bodyToString: ->
        body = @production.body[..]
        body[@dotPosition] = ".#{ body[@dotPosition] or '' }"
        body.join ' '
      toString: ->
        "#{ @production.head } -> #{ do @bodyToString }#{
          if @follows.length
            " #lookaheads= #{ @follows.join ' ' }"
          else '' }"

    ItemSet: Set.prototype.construct
      afterconstructor: ->
        @reductions = []
        @goes = {}
        @edges = {}
        @shifts = no
        @inadequate = no
        do @hashItems
      hashItems: (items) ->
        items ?= @_items
        @hash_ ?= {}
        @hashItem item for item in items by -1
      hashItem: (item) ->
        @hash_[item.id] = yes
      concat: (set) ->
        items = set._items or set
        @hashItems items
        @_items.push items...
        @
      push: (item) ->
        @hashItem item
        @_items.push item
      contains: (item) ->
        @hash_[item.id]
      valueOf: ->
        val =
          @_items
          .map (a) -> a.id
          .sort()
          .join '|'
        @valueOf = -> val
        val

    closureOperation: (itemSet) ->
      closureSet = new @ItemSet
      set = itemSet
      syms = {}
      loop
        itemQueue = new Set
        closureSet.concat set
        set.forEach (item) =>
          {markedSymbol: symbol} = item

          # if token is a non-terminal, recursively add closures
          if symbol and @nonterminals[symbol]
            unless syms[symbol]
              @nonterminals[symbol].productions.forEach (production) =>
                newItem = new @Item production, 0
                itemQueue.push newItem unless closureSet.contains newItem
              syms[symbol] = yes
          else if not symbol
            # reduction
            closureSet.reductions.push item
            closureSet.inadequate = closureSet.reductions.length > 1 or closureSet.shifts
          else
            # shift
            closureSet.shifts = yes
            closureSet.inadequate = closureSet.reductions.length > 0

        break if do itemQueue.isEmpty

        set = itemQueue

      closureSet

    # Pushes a unique state into the que. Some parsing algorithms may perform additional operations
    canonicalCollectionInsert: (symbol, itemSet, states, stateNum) ->
      gotoSet = @gotoOperation itemSet, symbol
      gotoSet.predecessors ?= {}
      # add gotoSet to que if not empty or duplicate
      unless do gotoSet.isEmpty
        val = do gotoSet.valueOf
        i = states.has[val]
        if i is -1 or not i?
          states.has[val] = do states.size
          itemSet.edges[symbol] = do states.size # store goto transition for table
          states.push gotoSet
          gotoSet.predecessors[symbol] = [stateNum]
        else
          itemSet.edges[symbol] = i # store goto transition for table
          states.item(i).predecessors[symbol].push stateNum

    gotoOperation: (itemSet, symbol) ->
      gotoSet = new @ItemSet(
        new @Item(
          production
          dotPosition + 1
          follows
          n
        ) for n, {markedSymbol, production, dotPosition, follows} of itemSet when markedSymbol is symbol
      )

      return gotoSet if do gotoSet.isEmpty
      @closureOperation gotoSet

    generate: (opt) ->
      opt = typal.mix.call {}, @options, opt
      code = ''

      # check for illegal identifier
      opt.moduleName = 'parser' unless opt.moduleName?.match /^[A-Za-z_$][A-Za-z0-9_$]*$/

      switch opt.moduleType
        when 'js'
          @generateModule opt
        when 'amd'
          @generateAMDModule opt
        else
          @generateCommonJSModule opt

    generateAMDModule: (opt) ->
      opt = typal.mix.call {}, @options, opt

      module = do @generateModule_
      """


      define(function(require){
      #{ module.commonCode }
      var parser = #{ module.moduleCode }
      #{ @moduleInclude }
      #{
        if @lexer?.generateModule
          """

          #{ do @lexer.generateModule }
          parser.lexer = lexer;
          """
        else ''
      }
      return parser;
      });
      """

    generateCommonJSModule: (opt) ->
      opt = typal.mix.call {}, @options, opt
      moduleName = opt.moduleName or 'parser'
      """
      #{ @generateModule opt }


      if (typeof require !== 'undefined' && typeof exports !== 'undefined') {
      exports.parser = #{ moduleName };
      exports.Parser = #{ moduleName }.Parser;
      exports.parse = function () { return #{ moduleName }.parse.apply(#{ moduleName }, arguments); };
      exports.main = #{ String(opt.moduleMain or commonjsMain) };
      if (typeof module !== 'undefined' && require.main === module) {
        exports.main(process.argv.slice(1));
      }
      }
      """

    generateModule: (opt) ->
      opt = typal.mix.call {}, @options, opt
      moduleName = opt.moduleName or 'parser'
      """
      /* parser generated by jison #{ version } */
      /*
        Returns a Parser object of the following structure:

        Parser: {
          yy: {}
        }

        Parser.prototype: {
          yy: {},
          trace: function(),
          symbols_: {associative list: name ==> number},
          terminals_: {associative list: number ==> name},
          productions_: [...],
          performAction: function anonymous(yytext, yyleng, yylineno, yy, yystate, $$, _$),
          table: [...],
          defaultActions: {...},
          parseError: function(str, hash),
          parse: function(input),

          lexer: {
            EOF: 1,
            parseError: function(str, hash),
            setInput: function(input),
            input: function(),
            unput: function(str),
            more: function(),
            less: function(n),
            pastInput: function(),
            upcomingInput: function(),
            showPosition: function(),
            test_match: function(regex_match_array, rule_index),
            next: function(),
            lex: function(),
            begin: function(condition),
            popState: function(),
            _currentRules: function(),
            topState: function(),
            pushState: function(condition),

            options: {
              ranges: boolean           (optional: true ==> token location info will include a .range[] member)
              flex: boolean             (optional: true ==> flex-like lexing behaviour where the rules are tested exhaustively to find the longest match)
              backtrack_lexer: boolean  (optional: true ==> lexer regexes are tested in order and for each matching regex the action code is invoked; the lexer terminates the scan when a token is returned by the action code)
            },

            performAction: function(yy, yy_, $avoiding_name_collisions, YY_START),
            rules: [...],
            conditions: {associative list: name ==> set},
          }
        }


        token location info (@$, _$, etc.): {
          first_line: n,
          last_line: n,
          first_column: n,
          last_column: n,
          range: [start_number, end_number]       (where the numbers are indexes into the input string, regular zero-based)
        }


        the parseError function receives a 'hash' object with these members for lexer and parser errors: {
          text:        (matched text)
          token:       (the produced terminal token, if any)
          line:        (yylineno)
        }
        while parser (grammar) errors will also provide these members, i.e. parser errors deliver a superset of attributes: {
          loc:         (yylloc)
          expected:    (string describing the set of expected tokens)
          recoverable: (boolean: TRUE when the parser has a error recovery rule available for this particular error)
        }
      */
      #{ unless moduleName.match /\./ then 'var ' else '' }#{ moduleName } = #{ do @generateModuleExpr }
      """

    generateModuleExpr: ->
      module = do @generateModule_

      """
      (function(){
      #{ module.commonCode }
      var parser = #{ module.moduleCode }
      #{ @moduleInclude }#{
        if @lexer?.generateModule
          """
          #{ do @lexer.generateModule }
          parser.lexer = lexer;
          """
        else ''
      }
      function Parser () {
        this.yy = {};
      }
      Parser.prototype = parser;parser.Parser = Parser;
      return new Parser;
      })();
      """

    # Generates the code of the parser module, which consists of two parts:
    # - module.commonCode: initialization code that should be placed before the module
    # - module.moduleCode: code that creates the module object
    generateModule_: do ->
      addTokenStack = (fn) ->
        parseFn = fn
        try
          ast = esprima.parse parseFn
          stackAst = esprima.parse String(tokenStackLex)).body[0]
          stackAst.id.name = 'lex'

          labeled = JSONSelect.match ':has(:root > .label > .name:val("_token_stack"))', ast

          labeled[0].body = stackAst

          escodegen
          .generate ast
          .replace /_token_stack:\s?/, ''
          .replace /\\\\n/g, '\\n'
        catch e
          parseFn

      # lex function that supports token stacks
      tokenStackLex = ->
        token = tstack.pop() or lexer.lex() or EOF
        # if token isn't its numeric value, convert
        return token if typeof token is 'number'

        if token instanceof Array
          tstack = token
          token = tstack.pop()
        token = self.symbols_[token] or token

      # returns parse function without error recovery code
      removeErrorRecovery = (fn) ->
        parseFn = fn
        try
          ast = esprima.parse parseFn

          labeled = JSONSelect.match ':has(:root > .label > .name:val("_handle_error"))', ast
          reduced_code = labeled[0].body.consequent.body[3].consequent.body
          reduced_code[0] = labeled[0].body.consequent.body[1]     # remove the line: error_rule_depth = locateNearestErrorRecoveryRule(state);
          reduced_code[4].expression.arguments[1].properties.pop() # remove the line: 'recoverable: error_rule_depth !== false'
          labeled[0].body.consequent.body = reduced_code

          escodegen
          .generate ast
          .replace /_handle_error:\s?/, ''
          .replace /\\\\n/g, '\\n'
        catch e
          parseFn

      ->
        parseFn = String parser.parse
        parseFn = removeErrorRecovery parseFn unless @hasErrorRecovery
        parseFn = addTokenStack parseFn if @options['token-stack']

        # Generate code with fresh variable names
        nextVariableId = 0
        tableCode = @generateTableCode @table

        # Generate the initialization code
        commonCode: tableCode.commonCode

        # Generate the module creation code
        moduleCode:
          """
          { trace: #{ String(@trace or parser.trace) }
          yy: {},
          symbols_: #{ JSON.stringify @symbols_ },
          terminals_: #{ JSON.stringify(@terminals_).replace(/"([0-9]+)":/g,"$1:") },
          productions_: #{ JSON.stringify @productions_ },
          performAction: #{ String @performAction },
          table: #{ tableCode.moduleCode },
          defaultActions: #{ JSON.stringify(this.defaultActions).replace(/"([0-9]+)":/g,"$1:") },
          parseError: #{ String(@parseError or (if @hasErrorRecovery then traceParseError else parser.parseError)) },
          parse: #{ parseFn }
          };
          """

    createParser: ->
      p = eval do @generateModuleExpr

      # for debugging
      p.productions = @productions

      bind = (method) =>
        =>
          @lexer = p.lexer
          @[method].apply @, arguments

      # backwards compatability
      p.lexer = @lexer
      p[method] = bind method for method in [
        'generate'
        'generateAMDModule'
        'generateModule'
        'generateCommonJSModule'
      ]

      p


  // Generate code that represents the specified parser table
  lrGeneratorMixin.generateTableCode = function (table) {
      var moduleCode = JSON.stringify(table);
      var variables = [createObjectCode];

      // Don't surround numerical property name numbers in quotes
      moduleCode = moduleCode.replace(/"([0-9]+)"(?=:)/g, "$1");

      // Replace objects with several identical values by function calls
      // e.g., { 1: [6, 7]; 3: [6, 7], 4: [6, 7], 5: 8 } = o([1, 3, 4], [6, 7], { 5: 8 })
      moduleCode = moduleCode.replace(/\{\d+:[^\}]+,\d+:[^\}]+\}/g, function (object) {
          // Find the value that occurs with the highest number of keys
          var value, frequentValue, key, keys = {}, keyCount, maxKeyCount = 0,
              keyValue, keyValues = [], keyValueMatcher = /(\d+):([^:]+)(?=,\d+:|\})/g;

          while ((keyValue = keyValueMatcher.exec(object))) {
              // For each value, store the keys where that value occurs
              key = keyValue[1];
              value = keyValue[2];
              keyCount = 1;

              if (!(value in keys)) {
                  keys[value] = [key];
              } else {
                  keyCount = keys[value].push(key);
              }
              // Remember this value if it is the most frequent one
              if (keyCount > maxKeyCount) {
                  maxKeyCount = keyCount;
                  frequentValue = value;
              }
          }
          // Construct the object with a function call if the most frequent value occurs multiple times
          if (maxKeyCount > 1) {
              // Collect all non-frequent values into a remainder object
              for (value in keys) {
                  if (value !== frequentValue) {
                      for (var k = keys[value], i = 0, l = k.length; i < l; i++) {
                          keyValues.push(k[i] + ':' + value);
                      }
                  }
              }
              keyValues = keyValues.length ? ',{' + keyValues.join(',') + '}' : '';
              // Create the function call `o(keys, value, remainder)`
              object = 'o([' + keys[frequentValue].join(',') + '],' + frequentValue + keyValues + ')';
          }
          return object;
      });

      // Count occurrences of number lists
      var list;
      var lists = {};
      var listMatcher = /\[[0-9,]+\]/g;

      while (list = listMatcher.exec(moduleCode)) {
          lists[list] = (lists[list] || 0) + 1;
      }

      // Replace frequently occurring number lists with variables
      moduleCode = moduleCode.replace(listMatcher, function (list) {
          var listId = lists[list];
          // If listId is a number, it represents the list's occurrence frequency
          if (typeof listId === 'number') {
              // If the list does not occur frequently, represent it by the list
              if (listId === 1) {
                  lists[list] = listId = list;
              // If the list occurs frequently, represent it by a newly assigned variable
              } else {
                  lists[list] = listId = createVariable();
                  variables.push(listId + '=' + list);
              }
          }
          return listId;
      });

      // Return the variable initialization code and the table code
      return {
          commonCode: 'var ' + variables.join(',') + ';',
          moduleCode: moduleCode
      };
  };
  // Function that extends an object with the given value for all given keys
  // e.g., o([1, 3, 4], [6, 7], { x: 1, y: 2 }) = { 1: [6, 7]; 3: [6, 7], 4: [6, 7], x: 1, y: 2 }
  var createObjectCode = 'o=function(k,v,o,l){' +
      'for(o=o||{},l=k.length;l--;o[k[l]]=v);' +
      'return o}';

  // Creates a variable with a unique name
  function createVariable() {
      var id = nextVariableId++;
      var name = '$V';

      do {
          name += variableTokens[id % variableTokensLength];
          id = ~~(id / variableTokensLength);
      } while (id !== 0);

      return name;
  }

  var nextVariableId = 0;
  var variableTokens = '0123456789abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_$';
  var variableTokensLength = variableTokens.length;

  // default main method for generated commonjs modules
  function commonjsMain (args) {
      if (!args[1]) {
          console.log('Usage: '+args[0]+' FILE');
          process.exit(1);
      }
      var source = require('fs').readFileSync(require('path').normalize(args[1]), "utf8");
      return exports.parser.parse(source);
  }

  // debug mixin for LR parser generators

  function printAction (a, gen) {
      var s = a[0] == 1 ? 'shift token (then go to state '+a[1]+')' :
          a[0] == 2 ? 'reduce by rule: '+gen.productions[a[1]] :
                      'accept' ;

      return s;
  }

  var lrGeneratorDebug = {
      beforeparseTable: function () {
          this.trace("Building parse table.");
      },
      afterparseTable: function () {
          var self = this;
          if (this.conflicts > 0) {
              this.resolutions.forEach(function (r, i) {
                  if (r[2].bydefault) {
                      self.warn('Conflict at state: ',r[0], ', token: ',r[1], "\n  ", printAction(r[2].r, self), "\n  ", printAction(r[2].s, self));
                  }
              });
              this.trace("\n"+this.conflicts+" Conflict(s) found in grammar.");
          }
          this.trace("Done.");
      },
      aftercanonicalCollection: function (states) {
          var trace = this.trace;
          trace("\nItem sets\n------");

          states.forEach(function (state, i) {
              trace("\nitem set",i,"\n"+state.join("\n"), '\ntransitions -> ', JSON.stringify(state.edges));
          });
      }
  };

  var parser = typal.beget();

  parser.trace = generator.trace;
  parser.warn = generator.warn;
  parser.error = generator.error;

  function traceParseError (err, hash) {
      this.trace(err);
  }

  function parseError (str, hash) {
      if (hash.recoverable) {
          this.trace(str);
      } else {
          var error = new Error(str);
          error.hash = hash;
          throw error;
      }
  }

  parser.parseError = lrGeneratorMixin.parseError = parseError;

  /*
   * LR(0) Parser
   * */

  var lr0 = generator.beget(lookaheadMixin, lrGeneratorMixin, {
      type: "LR(0)",
      afterconstructor: function lr0_afterconstructor () {
          this.buildTable();
      }
  });

  var LR0Generator = exports.LR0Generator = lr0.construct();

  /*
   * Simple LALR(1)
   * */

  var lalr = generator.beget(lookaheadMixin, lrGeneratorMixin, {
      type: "LALR(1)",

      afterconstructor: function (grammar, options) {
          if (this.DEBUG) this.mix(lrGeneratorDebug, lalrGeneratorDebug); // mixin debug methods

          options = options || {};
          this.states = this.canonicalCollection();
          this.terms_ = {};

          var newg = this.newg = typal.beget(lookaheadMixin,{
              oldg: this,
              trace: this.trace,
              nterms_: {},
              DEBUG: false,
              go_: function (r, B) {
                  r = r.split(":")[0]; // grab state #
                  B = B.map(function (b) { return b.slice(b.indexOf(":")+1); });
                  return this.oldg.go(r, B);
              }
          });
          newg.nonterminals = {};
          newg.productions = [];

          this.inadequateStates = [];

          // if true, only lookaheads in inadequate states are computed (faster, larger table)
          // if false, lookaheads for all reductions will be computed (slower, smaller table)
          this.onDemandLookahead = options.onDemandLookahead || false;

          this.buildNewGrammar();
          newg.computeLookaheads();
          this.unionLookaheads();

          this.table = this.parseTable(this.states);
          this.defaultActions = findDefaults(this.table);
      },

      lookAheads: function LALR_lookaheads (state, item) {
          return (!!this.onDemandLookahead && !state.inadequate) ? this.terminals : item.follows;
      },
      go: function LALR_go (p, w) {
          var q = parseInt(p, 10);
          for (var i=0;i<w.length;i++) {
              q = this.states.item(q).edges[w[i]] || q;
          }
          return q;
      },
      goPath: function LALR_goPath (p, w) {
          var q = parseInt(p, 10),t,
              path = [];
          for (var i=0;i<w.length;i++) {
              t = w[i] ? q+":"+w[i] : '';
              if (t) this.newg.nterms_[t] = q;
              path.push(t);
              q = this.states.item(q).edges[w[i]] || q;
              this.terms_[t] = w[i];
          }
          return {path: path, endState: q};
      },
      # every disjoint reduction of a nonterminal becomes a produciton in G'
      buildNewGrammar: function LALR_buildNewGrammar () {
          var self = this,
              newg = this.newg;

          this.states.forEach(function (state, i) {
              state.forEach(function (item) {
                  if (item.dotPosition === 0) {
                      // new symbols are a combination of state and transition symbol
                      var symbol = i+":"+item.production.head;
                      self.terms_[symbol] = item.production.head;
                      newg.nterms_[symbol] = i;
                      if (!newg.nonterminals[symbol])
                          newg.nonterminals[symbol] = new Nonterminal(symbol);
                      var pathInfo = self.goPath(i, item.production.body);
                      var p = new Production(symbol, pathInfo.path, newg.productions.length);
                      newg.productions.push(p);
                      newg.nonterminals[symbol].productions.push(p);

                      // store the transition that get's 'backed up to' after reduction on path
                      var body = item.production.body.join(' ');
                      var goes = self.states.item(pathInfo.endState).goes;
                      if (!goes[body])
                          goes[body] = [];
                      goes[body].push(symbol);

                      //self.trace('new production:',p);
                  }
              });
              if (state.inadequate)
                  self.inadequateStates.push(i);
          });
      },
      unionLookaheads: function LALR_unionLookaheads () {
          var self = this,
              newg = this.newg,
              states = !!this.onDemandLookahead ? this.inadequateStates : this.states;

          states.forEach(function union_states_forEach (i) {
              var state = typeof i === 'number' ? self.states.item(i) : i,
                  follows = [];
              if (state.reductions.length)
              state.reductions.forEach(function union_reduction_forEach (item) {
                  var follows = {};
                  for (var k=0;k<item.follows.length;k++) {
                      follows[item.follows[k]] = true;
                  }
                  state.goes[item.production.body.join(' ')].forEach(function reduction_goes_forEach (symbol) {
                      newg.nonterminals[symbol].follows.forEach(function goes_follows_forEach (symbol) {
                          var terminal = self.terms_[symbol];
                          if (!follows[terminal]) {
                              follows[terminal]=true;
                              item.follows.push(terminal);
                          }
                      });
                  });
                  //self.trace('unioned item', item);
              });
          });
      }
  });

  var LALRGenerator = exports.LALRGenerator = lalr.construct();

  // LALR generator debug mixin

  var lalrGeneratorDebug = {
      trace: function trace () {
          Jison.print.apply(null, arguments);
      },
      beforebuildNewGrammar: function () {
          this.trace(this.states.size()+" states.");
          this.trace("Building lookahead grammar.");
      },
      beforeunionLookaheads: function () {
          this.trace("Computing lookaheads.");
      }
  };

  /*
   * Lookahead parser definitions
   *
   * Define base type
   * */
  var lrLookaheadGenerator = generator.beget(lookaheadMixin, lrGeneratorMixin, {
      afterconstructor: function lr_aftercontructor () {
          this.computeLookaheads();
          this.buildTable();
      }
  });

  /*
   * SLR Parser
   * */
  var SLRGenerator = exports.SLRGenerator = lrLookaheadGenerator.construct({
      type: "SLR(1)",

      lookAheads: function SLR_lookAhead (state, item) {
          return this.nonterminals[item.production.head].follows;
      }
  });


  /*
   * LR(1) Parser
   * */
  var lr1 = lrLookaheadGenerator.beget({
      type: "Canonical LR(1)",

      lookAheads: function LR_lookAheads (state, item) {
          return item.follows;
      },
      Item: lrGeneratorMixin.Item.prototype.construct({
          afterconstructor: function () {
              this.id = this.production.id+'a'+this.dotPosition+'a'+this.follows.sort().join(',');
          },
          eq: function (e) {
              return e.id === this.id;
          }
      }),

      closureOperation: function LR_ClosureOperation (itemSet /*, closureSet*/) {
          var closureSet = new this.ItemSet();
          var self = this;

          var set = itemSet,
              itemQueue, syms = {};

          do {
          itemQueue = new Set();
          closureSet.concat(set);
          set.forEach(function (item) {
              var symbol = item.markedSymbol;
              var b, r;

              // if token is a nonterminal, recursively add closures
              if (symbol && self.nonterminals[symbol]) {
                  r = item.remainingHandle();
                  b = self.first(item.remainingHandle());
                  if (b.length === 0 || item.production.nullable || self.nullable(r)) {
                      b = b.concat(item.follows);
                  }
                  self.nonterminals[symbol].productions.forEach(function (production) {
                      var newItem = new self.Item(production, 0, b);
                      if(!closureSet.contains(newItem) && !itemQueue.contains(newItem)) {
                          itemQueue.push(newItem);
                      }
                  });
              } else if (!symbol) {
                  // reduction
                  closureSet.reductions.push(item);
              }
          });

          set = itemQueue;
          } while (!itemQueue.isEmpty());

          return closureSet;
      }
  });

  var LR1Generator = exports.LR1Generator = lr1.construct();

  /*
   * LL Parser
   * */
  ll = generator.beget lookaheadMixin,
    type: 'LL(1)'

    afterconstructor: ->
      do @computeLookaheads
      @table = @parseTable @productions
    parseTable: (productions) ->
      table = {}
      productions.forEach (production, productionIndex) =>
        {head, first, body} = production
        row = table[head] or {}
        tokens = first
        Set.union tokens, @nonterminals[head].follows if @nullable body
        tokens.forEach (token) =>
          if row[token]
            row[token].push productionIndex
            @conflicts++
          else
            row[token] = [productionIndex]
        table[head] = row
      table

  var LLGenerator = exports.LLGenerator = ll.construct();

  Jison.Generator = (g, options) ->
    opt = typal.mix.call {}, g.options, options
    switch opt.type
      when 'lr0'
        new LR0Generator g, opt
      when 'slr'
        new SLRGenerator g, opt
      when 'lr'
        new LR1Generator g, opt
      when 'll'
        new LLGenerator g, opt
      else
        new LALRGenerator g, opt

  (g, options) ->
    Jison.Generator g, options
    .createParser()

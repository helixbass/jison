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
  isNumber = (obj) ->
    typeof obj is 'number'
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

  class Nonterminal
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

  class Production
    constructor: (opts) ->
      {@head, @body, @id, @precedence} = opts
      @precedence ?= 0
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

      @mix generatorDebugMixin if @DEBUG

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
      @actionGroups = {}

      @hasErrorRecovery = no

      @symbols_ = {} # symbol => symbolId
      @symbols = []
      # add error symbol; will be third symbol, or "2" ($accept, $end, error)
      @addSymbol 'error'

      @productions = []
      @productions_ = [0] # [..., [headSymbolId, bodyLength], ...]
      @nonterminals = {}
      for own head, bodyActions of bnf
        @addSymbol head
        @addNonterminal head

        @buildProduction { bodyAction, head } for bodyAction in toList bodyActions, (str) -> str.split /\s*\|\s*/g

      for action, caseClauses of @actionGroups
        actions.push caseClauses.join(' '), action, 'break;'

      @terminals = [] # [..., symbol, ...]
      @terminals_ = {} # symbolId => symbol
      each @symbols_, (symbolId, symbol) =>
        return if @nonterminals[symbol]

        @terminals.push symbol
        @terminals_[symbolId] = symbol

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

    buildProduction: ({bodyAction, head}) ->
      @addProduction do =>
        if isArray bodyAction
          [body, action, opts] = bodyAction
          body = toList body
          if isString action
            actionSpecified = yes
          else
            opts = action
        else
          body =
            @stripAliases bodyAction
            .trim().split ' '

        for symbol in body
          @hasErrorRecovery = yes if symbol is 'error'
          @addSymbol symbol

        newProductionId = @productions.length + 1
        (@actionGroups[@replaceActionVars { action, body }] ?= [])
        .push "case #{ newProductionId }:" if actionSpecified

        @setMissingPrecedence new Production {
          head
          body: body.map @stripAliases
          id: newProductionId
          precedence: @operators[opts.prec].precedence if opts and @operators[opts.prec]
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

    addProduction: ( production ) ->
      {head, body} = production
      @productions.push production
      @productions_.push [
        @symbols_[head]
        if body[0] is ''
          0
        else
          body.length
      ]
      @nonterminals[head].productions.push production

    augmentGrammar: ({start, startSymbol}) ->
      throw new Error 'Grammar error: must have at least one rule.' unless @productions.length
      # use specified start symbol, or default to first user defined production
      @startSymbol = start or startSymbol or @productions[0].head
      throw new Error 'Grammar error: startSymbol must be a non-terminal found in your grammar.' unless @nonterminals[@startSymbol]
      @EOF = '$end'

      # add new first/starting production
      acceptProduction = new Production
        head: '$accept'
        body: [@startSymbol, @EOF]
        id: 0
      @productions.unshift acceptProduction

      # prepend parser tokens
      @symbols.unshift '$accept', @EOF
      @symbols_.$accept = 0
      @symbols_[@EOF] = 1
      @addNonterminal '$accept', (acceptNonterminal) ->
        acceptNonterminal.productions.push acceptProduction
      @terminals.unshift @EOF

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

  generatorDebugMixin =
    trace: ->
      Jison.print arguments...
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
      @mix lookaheadDebugMixin if @DEBUG

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


  lookaheadDebugMixin =
    beforenullableSets: ->
      @trace 'Computing Nullable sets.'
    beforefirstSets: ->
      @trace 'Computing First sets.'
    beforefollowSets: ->
      @trace 'Computing Follow sets.'
    afterfollowSets: ->
      each @nonterminals, (nonterminal) =>
        @trace nonterminal, '\n'

  ###
  # Mixin for common LR parser behavior
  ###
  lrGeneratorMixin =
    buildTable: ->
      @mix lrGeneratorDebugMixin if @DEBUG

      do @canonicalCollection
      @table = do @parseTable
      @defaultActions = do @findDefaults

    ###
    # Create unique set of item sets
    ###
    canonicalCollection: ->
      firstState =
        @closureOperation(
          new @Item
            production: @productions[0]
            follows: [@EOF]
        )
      @states = []
      @states.has = {}
      @newOrExistingStateNum firstState

      stateNum = -1
      while ++stateNum isnt @states.length
        state = @states[stateNum]
        @canonicalCollectionInsert {
          markedSymbol, state
        } for {markedSymbol} in state._items when markedSymbol and markedSymbol isnt @EOF

      @states

    Item: class Item
      constructor: (opts) ->
        {@production, @dotPosition, @follows} = opts
        @dotPosition ?= 0
        @follows ?= []
        @id = parseInt "#{ @production.id }a#{ @dotPosition }a#{ @follows.sort().join ',' }", 36
        @markedSymbol = @production.body[@dotPosition]
      remainingBody: ->
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

    ItemSet: class extends Set
      constructor: ->
        super
        @reductions = []
        @goes = {}
        @edges = {} # symbol => gotoStateNum
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
          .map ({id}) -> id
          .sort()
          .join '|'
        @valueOf = -> val
        val

    _closureOperation: ({itemSet, ifReduction, ifNonterminal, ifTerminal}) ->
      itemSet = new @ItemSet arguments... unless itemSet instanceof @ItemSet
      return itemSet if do itemSet.isEmpty

      closureSet = new @ItemSet
      set = itemSet
      alreadyAddedNonterminals = {}
      loop
        itemQueue = new Set
        closureSet.concat set
        set.forEach (item) =>
          {markedSymbol} = item

          if not markedSymbol
            # reduction
            closureSet.reductions.push item
            ifReduction? { closureSet, item }
          else if @nonterminals[markedSymbol]
            # if token is a non-terminal, recursively add closures
            ifNonterminal? { item, itemQueue, markedSymbol, closureSet, alreadyAddedNonterminals }
          else
            # shift
            ifTerminal? { closureSet }

        break if do itemQueue.isEmpty

        set = itemQueue

      closureSet

    closureOperation: (itemSet) ->
      @_closureOperation {
        itemSet
        ifReduction: ({ closureSet, item }) ->
          closureSet.inadequate = closureSet.reductions.length > 1 or closureSet.shifts
        ifNonterminal: ({ itemQueue, closureSet, markedSymbol, alreadyAddedNonterminals }) =>
          unless alreadyAddedNonterminals[markedSymbol]
            @nonterminals[markedSymbol].productions.forEach (production) =>
              newItem = new @Item { production }
              itemQueue.push newItem unless closureSet.contains newItem
            alreadyAddedNonterminals[markedSymbol] = yes
        ifTerminal: ({closureSet}) ->
          closureSet.shifts = yes
          closureSet.inadequate = closureSet.reductions.length > 0
      }

    # Pushes a unique state into the que. Some parsing algorithms may perform additional operations
    canonicalCollectionInsert: ({markedSymbol, state}) ->
      # TODO: optimize not recalculating gotoSet for items (in same state) w/ same markedSymbol
      gotoSet = @gotoOperation { state, markedSymbol }
      # add gotoSet to states if not empty or duplicate
      return if do gotoSet.isEmpty
      state.edges[markedSymbol] = @newOrExistingStateNum gotoSet # store goto transition for table

    newOrExistingStateNum: (state) ->
      stateVal = do state.valueOf
      alreadyHasState = @states.has[stateVal]
      return alreadyHasState if alreadyHasState? and alreadyHasState isnt -1

      @states.push state
      newStateNum = @states.length - 1
      @states.has[stateVal] = newStateNum
      newStateNum

    gotoOperation: ({state, markedSymbol: _markedSymbol}) ->
      @closureOperation(
        new @Item {
          production
          dotPosition: dotPosition + 1
          follows
        } for {markedSymbol, production, dotPosition, follows} in state._items when markedSymbol is _markedSymbol
      )

    NONASSOC: 0
    parseTable: ->
      @table = [] # stateNum => { ..., symbolId => action, ... } where action looks like:
      # [SHIFT, gotoStateNum] or [REDUCE, productionId] or [ACCEPT] or just gotoStateNum (for post-reduce)

      conflictedStates = {}
      [@SHIFT, @REDUCE, @ACCEPT] = [1..3]

      for stateNum, state in @states
        {edges, _items, reductions} = state

        row = @table[stateNum] = {}

        # set shift and goto actions
        for inputSymbol, gotoStateNum of edges
          # for {markedSymbol} in _items when markedSymbol is inputSymbol
            # find shift and goto actions
            row[@symbols_[inputSymbol]] =
              if @nonterminals[inputSymbol]
                # store state to go to after a reduce
                gotoStateNum
              else
                [@SHIFT, gotoStateNum]

        # set accept action
        row[@symbols_[@EOF]] = [@ACCEPT] for {markedSymbol} in _items when markedSymbol is @EOF

        # set reductions and resolve potential conflicts
        reductions.forEach (item) =>
          {production} = item
          # if parser uses lookahead, only enumerate those terminals
          (@lookAheads?(state, item) ? @terminals)
          .forEach (reduceableInputSymbol) =>
            reduceableInputSymbolId = @symbols_[reduceableInputSymbol]
            action = row[reduceableInputSymbolId]

            # Reading a terminal and current position is at the end of a production, try to reduce
            if action
              solution = @resolveConflict {
                production
                operator: @operators[reduceableInputSymbol]
                reduce: [@REDUCE, production.id]
                shift:
                  if isArray action[0]
                    action[0]
                  else
                    action
              }
              @resolutions.push [stateNum, reduceableInputSymbol, solution]
              if solution.bydefault
                @conflicts++
                unless @DEBUG
                  @warn """
                    Conflict in grammar: multiple actions possible when lookahead token is #{ reduceableInputSymbol } in state #{ stateNum }
                    - #{ @printAction solution.reduce }
                    - #{ @printAction solution.shift }
                  """
                  conflictedStates[stateNum] = yes
                if @options.noDefaultResolve
                  action = [action] unless isArray action[0]
                  action.push solution.reduce
              else
                action = solution.action
            else
              action = [@REDUCE, production.id]
            if action?.length
              row[reduceableInputSymbolId] = action
            else if action is @NONASSOC
              row[reduceableInputSymbolId] = undefined

      if @conflicts > 0 and not @DEBUG
        @warn """
        
          States with conflicts:#{
            each conflictedStates, (val, state) =>
              "State #{ state }  #{ @states[state].join '\n  ' }
          }
        """

      @table

    # resolves shift-reduce and reduce-reduce conflicts
    resolveConflict: ({production, operator, reduce, shift}) ->
      solution = {production, operator, reduce, shift}

      if shift[0] is @REDUCE
        solution.msg = 'Resolve R/R conflict (use first production declared in grammar.)'
        solution.action =
          if shift[1] < reduce[1]
            shift
          else
            reduce
        solution.bydefault = yes unless shift[1] is reduce[1]
        return solution

      extend solution,
        if production.precedence is 0 or not operator
          msg: 'Resolve S/R conflict (shift by default.)'
          bydefault: yes
          action: shift
        else if production.precedence < operator.precedence
          msg: 'Resolve S/R conflict (shift for higher precedent operator.)'
          action: shift
        else if production.precedence is operator.precedence
          switch operator.assoc
            when 'right'
              msg: 'Resolve S/R conflict (shift for right associative operator.)'
              action: shift
            when 'left'
              msg: 'Resolve S/R conflict (reduce for left associative operator.)'
              action: reduce
            when 'nonassoc'
              msg: 'Resolve S/R conflict (no action for non-associative operator.)'
              action: @NONASSOC
        else
          msg: 'Resolve conflict (reduce for higher precedent production.)'
          action: reduce

    # find states with only one action, a reduction
    findDefaults: ->
      @defaultActions = {} # stateNum => [REDUCE, productionId]
      @table.forEach (symbolActions, stateNum) =>
        return unless [symbolId for own symbolId of symbolActions].length is 1
        loneAction = symbolActions[symbolId]
        return unless loneAction[0] is @REDUCE

        # only one action in state and it's a reduction
        @defaultActions[stateNum] = loneAction

      @defaultActions

    generate: (opt) ->
      opt = extended @options, opt
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
      opt = extended @options, opt

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
      opt = extended @options, opt
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
      opt = extended @options, opt
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

    # Generate code that represents the specified parser table
    generateTableCode: ->
      moduleCode = JSON.stringify @table
      variables = [createObjectCode]

      # Don't surround numerical property name numbers in quotes
      moduleCode = moduleCode.replace(/"([0-9]+)"(?=:)/g, "$1");

      # Replace objects with several identical values by function calls
      # e.g., { 1: [6, 7]; 3: [6, 7], 4: [6, 7], 5: 8 } = o([1, 3, 4], [6, 7], { 5: 8 })
      moduleCode = moduleCode.replace(/\{\d+:[^\}]+,\d+:[^\}]+\}/g, function (object) {
        # Find the value that occurs with the highest number of keys
        var value, frequentValue, key, keys = {}, keyCount, maxKeyCount = 0,
            keyValue, keyValues = [], keyValueMatcher = /(\d+):([^:]+)(?=,\d+:|\})/g;

        while keyValue=keyValueMatcher.exec object
          # For each value, store the keys where that value occurs
          key = keyValue[1]
          value = keyValue[2]
          keyCount = 1

          if value not of keys
            keys[value] = [key]
          else
            keyCount = keys[value].push key
          # Remember this value if it is the most frequent one
          if keyCount > maxKeyCount
            maxKeyCount = keyCount;
            frequentValue = value;
        # Construct the object with a function call if the most frequent value occurs multiple times
        if maxKeyCount > 1
          # Collect all non-frequent values into a remainder object
          for (value in keys) {
              if (value !== frequentValue) {
                  for (var k = keys[value], i = 0, l = k.length; i < l; i++) {
                      keyValues.push(k[i] + ':' + value);
                  }
              }
          }
          keyValues = keyValues.length ? ',{' + keyValues.join(',') + '}' : '';
          # Create the function call `o(keys, value, remainder)`
          object = 'o([' + keys[frequentValue].join(',') + '],' + frequentValue + keyValues + ')';
        object

      # Count occurrences of number lists
      lists = {}
      listMatcher = ///
        \[
        [0-9,] +
        \]
      ///g

      while list=listMatcher.exec moduleCode
        lists[list] = (lists[list] or 0) + 1

      # Replace frequently occurring number lists with variables
      moduleCode = moduleCode.replace listMatcher, (list) ->
        listId = lists[list]
        # If listId is a number, it represents the list's occurrence frequency
        if isNumber listId
          # If the list does not occur frequently, represent it by the list
          if listId is 1
            lists[list] = listId = list
          # If the list occurs frequently, represent it by a newly assigned variable
          else
            lists[list] = listId = do createVariable
            variables.push "#{ listId }=#{ list }"
        listId

      # Return the variable initialization code and the table code
      {
        commonCode: "var #{ variables.join ',' };"
        moduleCode
      }

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

  # default main method for generated commonjs modules
  commonjsMain = (program, filename) ->
    unless filename
      console.log "Usage: #{ program } FILE"
      process.exit 1
    {readFileSync} = require 'fs'
    {normalize} = require 'path'
    source = readFileSync normalize(filename), 'utf8'
    exports.parser.parse source

  # debug mixin for LR parser generators
  lrGeneratorDebugMixin =
    beforeparseTable: ->
      @trace 'Building parse table.'
    afterparseTable: ->
      @printAction = (action) =>
        switch action[0]
          when 1 then "shift token (then go to state #{ action[1] })"
          when 2 then "reduce by rule: #{ @productions[action[1]]}"
          else        'accept'

      if @conflicts
        @resolutions.forEach ([state, token, {bydefault, reduce, shift}]) =>
          if bydefault
            @warn """
              Conflict at state: #{ state }, token: #{ token }
                #{ @printAction reduce }
                #{ @printAction shift }
            """
        @trace "\n#{ @conflicts } Conflict(s) found in grammar."
      @trace 'Done.'
    aftercanonicalCollection: (states) ->
      @trace """
      
      Item sets
      ------
      """

      states.forEach (state, i) =>
        @trace '\nitem set', i, "\n#{ state.join '\n' }", '\ntransitions -> ', JSON.stringify state.edges

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

  generators = {}
  typeFromNameRegex = /^(.+)(\d)$/
  registerGenerator = (name, klass) ->
    klass::type ?=
      if matched=typeFromNameRegex.exec name
        [baseName, numLookaheads] = matched
        "#{ do baseName.toUpperCase }(#{ numLookaheads })"
      else
        "#{ do name.toUpperCase }(1)"
    generators[name] = exports["#{ do name.toUpperCase }Generator"] = klass

  ###
  # LR(0) Parser
  ###
  registerGenerator 'lr0', generator.construct lookaheadMixin, lrGeneratorMixin,
    afterconstructor: ->
      do @buildTable

  ###
  # Simple LALR(1)
  ###
  registerGenerator 'lalr', generator.construct lookaheadMixin, lrGeneratorMixin,
    afterconstructor: function (grammar, options) {
        if (this.DEBUG) this.mix(lrGeneratorDebugMixin, lalrGeneratorDebug); // mixin debug methods

        options = options || {};
        this.canonicalCollection();
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

        this.table = this.parseTable();
        this.defaultActions = do @findDefaults
    },

    lookAheads: function LALR_lookaheads (state, item) {
        return (!!this.onDemandLookahead && !state.inadequate) ? this.terminals : item.follows;
    },
    go: function LALR_go (p, w) {
        var q = parseInt(p, 10);
        for (var i=0;i<w.length;i++) {
            q = this.states[q].edges[w[i]] || q;
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
            q = this.states[q].edges[w[i]] || q;
            this.terms_[t] = w[i];
        }
        { path, endState: q }
    # every disjoint reduction of a nonterminal becomes a produciton in G'
    buildNewGrammar: ->
        var self = this,
            newg = this.newg;

        this.states.forEach(function (state, i) {
            state.forEach(function (item) {
                if (item.dotPosition === 0) {
                    # new symbols are a combination of state and transition symbol
                    var symbol = i+":"+item.production.head;
                    self.terms_[symbol] = item.production.head;
                    newg.nterms_[symbol] = i;
                    if (!newg.nonterminals[symbol])
                        newg.nonterminals[symbol] = new Nonterminal(symbol);
                    var pathInfo = self.goPath(i, item.production.body);
                    var p = new Production(head: symbol, body: pathInfo.path, id: newg.productions.length);
                    newg.productions.push(p);
                    newg.nonterminals[symbol].productions.push(p);

                    # store the transition that get's 'backed up to' after reduction on path
                    var body = item.production.body.join(' ');
                    var goes = self.states[pathInfo.endState].goes;
                    if (!goes[body])
                        goes[body] = [];
                    goes[body].push(symbol);

                    #self.trace('new production:',p);
                }
            });
            if (state.inadequate)
                self.inadequateStates.push(i);
        });
    unionLookaheads: function LALR_unionLookaheads () {
        var self = this,
            newg = this.newg,
            states = !!this.onDemandLookahead ? this.inadequateStates : this.states;

        states.forEach(function union_states_forEach (i) {
            var state = typeof i === 'number' ? self.states[i] : i,
                follows = [];
            if (state.reductions.length)
            state.reductions.forEach(function union_reduction_forEach (item) {
                var follows = {};
                for (var k=0;k<item.follows.length;k++) {
                    follows[item.follows[k]] = true;
                state.goes[item.production.body.join(' ')].forEach(function reduction_goes_forEach (symbol) {
                    newg.nonterminals[symbol].follows.forEach(function goes_follows_forEach (symbol) {
                        var terminal = self.terms_[symbol];
                        if (!follows[terminal]) {
                            follows[terminal]=true;
                            item.follows.push(terminal);
                #self.trace('unioned item', item);

  # LALR generator debug mixin
  lalrGeneratorDebug =
    trace: ->
      Jison.print arguments...
    beforebuildNewGrammar: ->
      @trace "#{ @states.length } states."
      @trace 'Building lookahead grammar.'
    beforeunionLookaheads: ->
      @trace 'Computing lookaheads.'

  ###
  # Lookahead parser definitions
  #
  # Define base type
  ###
  lrLookaheadGenerator = generator.beget lookaheadMixin, lrGeneratorMixin,
    afterconstructor: ->
      do @computeLookaheads
      do @buildTable

  ###
  # SLR Parser
  ###
  registerGenerator 'slr', lrLookaheadGenerator.construct
    lookAheads: (state, item) ->
      @nonterminals[item.production.head].follows

  ###
  # LR(1) Parser
  ###
  registerGenerator 'lr1', lrLookaheadGenerator.construct
    type: 'Canonical LR(1)'

    lookAheads: (state, item) ->
      item.follows

    closureOperation: (itemSet) ->
      @_closureOperation {
        itemSet
        ifNonterminal: ({ item, itemQueue, markedSymbol, closureSet }) =>
          remainingBody = do item.remainingBody
          follows = @first remainingBody
          if follows.length is 0 or item.production.nullable or @nullable remainingBody
            follows = follows.concat item.follows
          @nonterminals[markedSymbol].productions.forEach (production) =>
            newItem = new @Item { production, follows }
            itemQueue.push newItem unless closureSet.contains(newItem) or itemQueue.contains newItem
      }

  ###
  # LL Parser
  ###
  registerGenerator 'll', generator.construct lookaheadMixin,
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

  Jison.Generator = (grammar, options) ->
    opt = extended grammar.options, options
    klass = generators[opt.type] ? generators.lalr
    new klass grammar, opt

  (grammar, options) ->
    Jison.Generator grammar, options
    .createParser()

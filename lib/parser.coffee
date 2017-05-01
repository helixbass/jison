parser =
  parse: (input, args...) ->
    stack = [0]
    tstack = [] # token stack
    vstack = [null] # semantic value stack
    lstack = [] # location stack
    yytext = ''
    yylineno = 0
    yyleng = 0
    recovering = 0
    TERROR = 2
    EOF = 1

    #this.reductionCount = this.shiftCount = 0;

    lexer = Object.create @lexer
    yy = {}
    # copy state
    yy[key] = val for own key, val of @yy

    lexer.setInput input, yy
    yy.lexer = lexer
    yy.parser = @
    lexer.yylloc ?= {}
    {yylloc} = lexer
    lstack.push yylloc

    {ranges} = lexer.options ? {}

    @parseError =
      if typeof yy.parseError is 'function'
        yy.parseError
      else
        Object.getPrototypeOf(@).parseError

    popStack = (n) ->
      stack.length = stack.length - 2 * n
      vstack.length = vstack.length - n
      lstack.length = lstack.length - n

# _token_stack:
    lex = =>
      token = lexer.lex() or EOF
      return token if typeof token is 'number'

      # if token isn't its numeric value, convert
      @symbols_[token] or token

    symbol = null
    loop
      # retrieve state number from top of stack
      [..., state] = stack

      # use default actions if available
      action =
        @defaultActions[state] ? do =>
          symbol = lex() unless symbol?
          # read action for current state and first input
          @table[state]?[symbol]

# _handle_error:
      # handle parse error
      # if (typeof action === 'undefined' || !action.length || !action[0]) {
      unless action?[0]
        # Return the rule stack depth where the nearest error rule can be found.
        # Return FALSE when no error recovery rule was found.
        locateNearestErrorRecoveryRule = (state) =>
          stack_probe = stack.length - 1
          depth = 0

          # try to recover from error
          loop
            # check for error recovery rule in this state
            return depth if TERROR.toString() in @table[state]
            return no if state is 0 or stack_probe < 2 # No suitable error recovery rule available.
            stack_probe -= 2 # popStack(1): [symbol, action]
            state = stack[stack_probe]
            ++depth

        unless recovering
          # first see if there's any chance at hitting an error recovery rule:
          error_rule_depth = locateNearestErrorRecoveryRule state

          # Report error
          expected =
            "'#{@terminals_[p]}'" for p of @table[state] when @terminals_[p] and p > TERROR
          errStr =
            "Parse error on line #{yylineno + 1}:#{
              if lexer.showPosition
                "\n#{ lexer.showPosition() }\nExpecting #{ expected.join ', ' }, got '#{ @terminals_[symbol] or symbol }'"
              else
                " Unexpected #{
                  if symbol == EOF
                    "end of input"
                  else
                    "'#{ @terminals_[symbol] or symbol }'" }"
            }"
          @parseError errStr, {
            text: lexer.match
            token: @terminals_[symbol] or symbol
            line: lexer.yylineno
            loc: yylloc
            expected
            recoverable: error_rule_depth isnt no
          }
        else if preErrorSymbol isnt EOF
          error_rule_depth = locateNearestErrorRecoveryRule state

        # just recovered from another error
        if recovering == 3
          throw new Error errStr or 'Parsing halted while starting to recover from another error.' if symbol is EOF or preErrorSymbol is EOF

          # discard current lookahead and grab another
          {yyleng, yytext, yylineno, yylloc} = lexer
          symbol = lex()

        # try to recover from error
        throw new Error errStr || 'Parsing halted. No suitable error recovery rule available.' if error_rule_depth is no
        popStack error_rule_depth

        preErrorSymbol =
          symbol unless symbol == TERROR # save the lookahead token
        symbol = TERROR # insert generic error symbol as new lookahead
        state = stack[stack.length-1]
        action = @table[state]?[TERROR]
        recovering = 3 # allow 3 real symbols to be shifted before reporting a new error

      # this shouldn't happen, unless resolve defaults are off
      throw new Error "Parse Error: multiple actions possible at state: #{state}, token: #{symbol}" if action[0] instanceof Array and action.length > 1

      switch action[0]
        when 1 # shift
          #this.shiftCount++;

          stack.push symbol
          vstack.push lexer.yytext
          lstack.push lexer.yylloc
          stack.push action[1] # push state
          symbol = null
          unless preErrorSymbol # normal execution/no error
            {yyleng, yytext, yylineno, yylloc} = lexer
            recovering-- if recovering > 0
          else
            # error just occurred, resume old lookahead f/ before error
            symbol = preErrorSymbol
            preErrorSymbol = null
        when 2 # reduce
          #this.reductionCount++;

          len = @productions_[action[1]][1]

          lstack_last = lstack[lstack.length - 1]
          lstack_len_last = lstack[lstack.length - (len or 1)]
          # perform semantic action
          yyval =
            $: vstack[vstack.length - len] # default to $$ = $1
            # default location, uses first token for firsts, last for lasts
            _$:
              first_line: lstack_len_last.first_line
              last_line: lstack_last.last_line
              first_column: lstack_len_last.first_column
              last_column: lstack_last.last_column
          if ranges
            yyval._$.range = [lstack_len_last.range[0], lstack_last.range[1]]
          r = @performAction.apply yyval, [yytext, yyleng, yylineno, yy, action[1], vstack, lstack, args...]
          return r if typeof r isnt 'undefined'

          # pop off stack
          if len
            stack  = stack.slice  0, -1 * len * 2
            vstack = vstack.slice 0, -1 * len
            lstack = lstack.slice 0, -1 * len

          stack.push @productions_[action[1]][0] # push nonterminal (reduce)
          vstack.push yyval.$
          lstack.push yyval._$
          # goto new state = @table[STATE][NONTERMINAL]
          newState = @table[stack[stack.length - 2]][stack[stack.length - 1]]
          stack.push newState
        when 3
          # accept
          return yes
    yes
  init: ({@table, @defaultActions, @performActions, @productions_, @symbols_, @terminals_}) ->

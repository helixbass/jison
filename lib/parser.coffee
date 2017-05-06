parser =
  parse: (input, args...) ->
    stack = [0] # [..., symbolId, stateNum, ...]
    tstack = [] # token stack
    vstack = [null] # semantic value stack
    lstack = [] # location stack
    yytext = ''
    yylineno = 0
    yyleng = 0
    recovering = 0
    TERROR = 2
    EOF = 1
    [SHIFT, REDUCE, ACCEPT] = [1..3]

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

    nextInputSymbolId = null
    loop
      [..., stateNum] = stack

      # use default actions if available
      action =
        @defaultActions[stateNum] ? do =>
          nextInputSymbolId ?= lex()
          # read action for current state and first input
          @table[stateNum]?[nextInputSymbolId]

# _handle_error:
      # handle parse error
      # if (typeof action === 'undefined' || !action.length || !action[0]) {
      unless action?[0]
        # Return the rule stack depth where the nearest error rule can be found.
        # Return FALSE when no error recovery rule was found.
        locateNearestErrorRecoveryRule = (stateNum) =>
          stack_probe = stack.length - 1
          depth = 0

          # try to recover from error
          loop
            # check for error recovery rule in this state
            return depth if TERROR.toString() in @table[stateNum]
            return no if stateNum is 0 or stack_probe < 2 # No suitable error recovery rule available.
            stack_probe -= 2 # popStack(1): [symbol, action]
            stateNum = stack[stack_probe]
            ++depth

        unless recovering
          # first see if there's any chance at hitting an error recovery rule:
          error_rule_depth = locateNearestErrorRecoveryRule stateNum

          # Report error
          expected =
            "'#{@terminals_[p]}'" for p of @table[stateNum] when @terminals_[p] and p > TERROR
          errStr =
            "Parse error on line #{yylineno + 1}:#{
              if lexer.showPosition
                "\n#{ lexer.showPosition() }\nExpecting #{ expected.join ', ' }, got '#{ @terminals_[nextInputSymbolId] or nextInputSymbolId }'"
              else
                " Unexpected #{
                  if nextInputSymbolId == EOF
                    "end of input"
                  else
                    "'#{ @terminals_[nextInputSymbolId] or nextInputSymbolId }'" }"
            }"
          @parseError errStr, {
            text: lexer.match
            token: @terminals_[nextInputSymbolId] or nextInputSymbolId
            line: lexer.yylineno
            loc: yylloc
            expected
            recoverable: error_rule_depth isnt no
          }
        else if preErrorSymbol isnt EOF
          error_rule_depth = locateNearestErrorRecoveryRule stateNum

        # just recovered from another error
        if recovering == 3
          throw new Error errStr or 'Parsing halted while starting to recover from another error.' if nextInputSymbolId is EOF or preErrorSymbol is EOF

          # discard current lookahead and grab another
          {yyleng, yytext, yylineno, yylloc} = lexer
          nextInputSymbolId = lex()

        # try to recover from error
        throw new Error errStr || 'Parsing halted. No suitable error recovery rule available.' if error_rule_depth is no
        popStack error_rule_depth

        preErrorSymbol =
          nextInputSymbolId unless nextInputSymbolId == TERROR # save the lookahead token
        nextInputSymbolId = TERROR # insert generic error symbol as new lookahead
        [..., stateNum] = stack
        action = @table[stateNum]?[TERROR]
        recovering = 3 # allow 3 real symbols to be shifted before reporting a new error

      # this shouldn't happen, unless resolve defaults are off
      throw new Error "Parse Error: multiple actions possible at state: #{stateNum}, token: #{nextInputSymbolId}" if action[0] instanceof Array and action.length > 1

      switch action[0]
        when SHIFT
          #this.shiftCount++;

          stack.push nextInputSymbolId, action[1] # gotoStateNum
          vstack.push lexer.yytext
          lstack.push lexer.yylloc
          nextInputSymbolId = null
          unless preErrorSymbol # normal execution/no error
            {yyleng, yytext, yylineno, yylloc} = lexer
            recovering-- if recovering > 0
          else
            # error just occurred, resume old lookahead f/ before error
            nextInputSymbolId = preErrorSymbol
            preErrorSymbol = null
        when REDUCE
          #this.reductionCount++;
          productionId = action[1]
          [headSymbolId, bodyLength] = @productions_[productionId]

          # perform semantic action
          yyval = do ->
            [..., lstack_last] = lstack
            lstack_len_last = lstack[lstack.length - (bodyLength or 1)]
            $: vstack[vstack.length - bodyLength] # default to $$ = $1
            # default location, uses first token for firsts, last for lasts
            _$:
              first_line: lstack_len_last.first_line
              last_line: lstack_last.last_line
              first_column: lstack_len_last.first_column
              last_column: lstack_last.last_column
              range: [lstack_len_last.range[0], lstack_last.range[1]] if ranges
          actionReturned =
            @performAction.apply yyval, [yytext, yyleng, yylineno, yy, productionId, vstack, lstack, args...]
          return actionReturned if actionReturned?

          popStack bodyLength if bodyLength
          [..., prevStateNum] = stack
          stack.push headSymbolId, @table[prevStateNum][headSymbolId] # post-reduce gotoStateNum
          vstack.push yyval.$
          lstack.push yyval._$
        when ACCEPT
          return yes
    yes
  init: ({@table, @defaultActions, @performActions, @productions_, @symbols_, @terminals_}) ->

###
# Introduces a typal object to make classical/prototypal patterns easier
# Plus some AOP sugar
#
# By Zachary Carter <zach@carter.name>
# MIT Licensed
###

typal = do ->
  create = Object.create ? (prototypeObj) ->
    F = ->
    F.prototype = prototypeObj
    new F
  position = /^(before|after)/

  # basic method layering
  # always returns original method's return value
  layerMethod = ({key, enhancingMethod, matched: [pos], existingMethod, methodName}) {
    @[methodName] =
      switch pos
        when 'after'
          ->
            ret = existingMethod.apply @, arguments
            enhancingMethod.apply @, [ret, arguments...]
            ret
        when 'before'
          ->
            enhancingMethod.apply @, arguments
            existingMethod.apply @, arguments

  # mixes each argument's own properties into calling object,
  # overwriting them or layering them. i.e. an object method 'meth' is
  # layered by mixin methods 'beforemeth' or 'aftermeth'
  mix = ->
    for mixin in arguments when mixin
      for own key, val in mixin
        if matched=key.match(position) and typeof (existingMethod=@[methodName=key.replace position, '']) is 'function'
          layerMethod.call @, {key, enhancingMethod: val, matched, existingMethod, methodName}
        else
          @[key] = val
    @

  # sugar for object begetting and mixing
  # - Object.create(typal).mix(etc, etc);
  # + typal.beget(etc, etc);
  beget = ->
    obj = create @
    return obj unless arguments.length
    mix.apply obj, arguments

  _construct = ->
    {constructor} = @
    Klass = @constructor = -> constructor.apply @, arguments
    Klass.prototype = @
    Klass.mix = mix # allow for easy singleton property extension
    Klass

  # extend object with own typalperties of each argument
  {
    mix, beget, _construct

    # Creates a new Class function based on an object with a constructor method
    construct: ->
      _construct.call beget.apply @, arguments

    # no op
    constructor: -> @
  }

exports.typal = typal if exports?

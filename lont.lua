--- 
--- Experimental stuff related to ontology.
---

local List = require "list"
local Type = require "Type"
local util = require "util"

local world = {}

world.records = 
{
  list = List{},
  map = {}
}

local record = {}

local indexer = function(f)
  return setmetatable({}, { __index = f })
end

local indexcaller = function(fi, fc)
  return setmetatable({}, { __index = fi, __call = fc })
end

record.def = function(name)
  if world.records[name] then
    error("a record named "..name.." already exists")
  end

  local r = {}
  world.records.map[name] = r
  world.records.list:push(r)

  r.name = name
  r.id = #world.records.list
  r.statements = {}

  return setmetatable({},
  {
    __index = function(self, k)
      local statement = r.statements[k]
      if not statement then
        statement = List{}
        r.statements[k] = statement
      end

      local chained 

      local function valuegetter(value)
        if type(value) == "string" then
          value = world.records[value] or value
        end
        statement:push(value)
        return chained
      end

      chained = setmetatable({}, 
      {
        __call = valuegetter,
        __index = self
      })

      return valuegetter
    end
  })
end

record.def "entity"

record.def "object"
  .subclass_of "entity"

record.def "physical object"
  .subclass_of "object"

record.def "natural physical object"
  .subclass_of "physical object"

record.def "fruit"
  .subclass_of 
    "natural physical object" 

record.def "apple"
  .subclass_of 
    "fruit"

record.def "organism"
  .subclass_of
    "physical object"

record.def "heterotroph"
  .subclass_of "organism"

record.def "animal"
  .subclass_of 
    "heterotroph"

record.def "vertebrate"
  .subclass_of 
    "animal"

record.def "mammal"
  .subclass_of 
    "vertebrate"

record.def "domesticated animal"
  .subclass_of 
    "animal"

record.def "domesticated mammal"
  .subclass_of 
    "domesticated animal"
    "mammal"
  
record.def "pet"
  .subclass_of 
    "domesticated animal"

record.def "house cat"
  .subclass_of "pet"

record.def "agent"
  .subclass_of "entity"

record.def "individual"
  .subclass_of 
    "organism"
    "agent"

record.def "person"
  .subclass_of "individual"

record.def "consumer"
  .subclass_of "heterotroph"

record.def "omnivore"
  .subclass_of
    "consumer"
    "animal"

record.def "human"
  .subclass_of
    "mammal"
    "person"
    "omnivore"

record.def "Samuel Johnson"
  .instance_of "human"
  .sex "male"
  .date_of_birth "18 September 1709"

record.def "Hodge"
  .instance_of "house cat"
  .owned_by "Samuel Johnson"

local query =
[[
  show ?item ?thing where
  {
    ?item sex [male].
  }
]]

local Query = Type.make()

Query.new = function()
  local o = {}
  o.vars = {}
  o.triples = List{}

  return setmetatable(o, Query)
end

local Triple = Type.make()

Triple.new = function(subject, predicate, object)
  local o = {}
  o.subject = subject
  o.predicate = predicate
  o.object = object
  return setmetatable(o, Triple)
end

local Var = Type.make()

Var.new = function(name)
  local o = {}
  o.name = name
  return setmetatable(o, Var)
end 

local Term = Type.make()

local RecordRef = Term:derive()

RecordRef.new = function(id)
  local o = {}
  o.id = id
  return setmetatable(o, RecordRef)
end

local parser = {}

parser.buffer = query
parser.offset = 1
parser.query = Query.new()

parser.errorHere = function(self, ...)
  local cut = self.buffer:sub(1, self.offset)
  local line = 1 + select(2, cut:gsub("\n", ""))
  local column = 1 + self.offset - select(3, cut:find(".*\n().*$"))

  io.write("error:"..line..":"..column..": ")
  io.write(...)
  io.write "\n"

  os.exit(1)
end

parser.expectToken = function(self, token)
  self:skipWhitespace()
  local start, stop = self.buffer:find("^"..token, self.offset)
  if not start then
    self:errorHere("expected '", token, "'")
  end
  self.offset = stop + 1
end

parser.skipWhitespace = function(self)
  local start, stop = self.buffer:find("%s*", self.offset)
  if start then
    self.offset = stop + 1
  end
end 

parser.checkPattern = function(self, pattern)
  self:skipWhitespace()
  local start, stop = self.buffer:find("^"..pattern, self.offset)
  if not start then
    return false
  end
  self.offset = stop + 1
  return self.buffer:sub(start, stop)
end

parser.parseShowVar = function(self)
  
end

parser.parseShowVars = function(self)
  while true do
    self:skipWhitespace()
    local var = self:checkPattern "%?[%w_]+"
    if not var then 
      return 
    end
  end
end

parser.parseTerm = function(self)
  local record_ref = self:checkPattern "%[.-%]"
  if record_ref then
    return RecordRef.new(record_ref:sub(2,-2))
  end

  self:errorHere("expected a term")
end

parser.findOrCreateVar = function(self,name)
  local var = self.query.vars[name]
  if not var then
    var = Var.new(name)
    self.query.vars[name] = var
  end
  return var
end

parser.parseVarOrTerm = function(self)
  self:skipWhitespace()

  local var = self:checkPattern "%?[%w_]+"
  if var then
    return (self:findOrCreateVar(var:sub(2)))
  end

  return (self:parseTerm())
end

parser.parsePredicate = function(self)
  local predicate = self:checkPattern "[%w_]+"
  if not predicate then
    self:errorHere("expected a predicate")
  end
  return predicate
end

parser.parseTriplesBlock = function(self)
  self:expectToken "{"

  while true do
    local subject = self:parseVarOrTerm()
    local predicate = self:parsePredicate()
    local object = self:parseVarOrTerm()

    self.query.triples:push(Triple.new(subject, predicate, object))

    self:expectToken "."

    if self:checkPattern "}" then
      break
    else
      self:errorHere("expected a triple or '}' to close block")
    end
  end
end

parser.parseShowQuery = function(self)
  self:parseShowVars()
  
  self:expectToken "where"

  self:parseTriplesBlock()
end

parser.parseQuery = function(self)
  self:skipWhitespace()
  self:expectToken "show"
  self:parseShowQuery()
end

parser:parseQuery()

local case_Var_RecordRef = function(var, ref, predicate)
  local matches = List{}

  local ref_record = world.records.map[ref.id]
  if not ref_record then
    error("no record named '"..ref.id.."'")
  end

  for record in world.records.list:each() do
    local statement = record.statements[predicate]
    if statement then
      for value in statement:each() do
        local val_record = world.records.map[value]
        if val_record == ref_record then
          matches:push(record)
        end
      end
    end
  end

  return matches
end

local case_Var = function(var, triple)
  if triple.object:is(RecordRef) then
    return (case_Var_RecordRef(var, triple.object, triple.predicate))
  else
    error("unhandled triple case")
  end
end

local matches

for triple in parser.query.triples:each() do
  if triple.subject:is(Var) then
    matches = case_Var(triple.subject, triple)
  else
    error "unhandled triple case"
  end
end

for match in matches:each() do
  print(match.name)
end


import Rgb.Lib.Enums
import Rgb.Schemas.Standard

/-!
# rgb-lib's schemas

The standard schema behind each asset schema rgb-lib supports, and the asset schema of a
schema id (`AssetSchema::try_from(SchemaId)`). PFA is in `rgb-schemas` only, so no asset
schema has its id.
-/

namespace Rgb.Lib

namespace AssetSchema

/-- Standard schema rules: the schema and its script libraries. -/
def rules : AssetSchema → SchemaRules
  | .nia => Schemas.niaRules | .uda => Schemas.udaRules | .cfa => Schemas.cfaRules
  | .ifa => Schemas.ifaRules | .bfa => Schemas.bfaRules

/-- The standard schema. -/
def schema (s : AssetSchema) : Schema := s.rules.schema

/-- The asset schema of a schema id, if rgb-lib supports it. -/
def ofSchemaId? (id : SchemaId) : Option AssetSchema := all.find? (·.schema.schemaId == id)

end AssetSchema

end Rgb.Lib

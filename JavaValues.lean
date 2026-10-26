import Std

namespace Argos.JavaValues

/-- Encoded record contents, including nullable Java metadata. -/
structure Image where
  id : String
  accumulator : String
  version : Int
  created : String
  updated : String
  deriving DecidableEq, Repr

/-- Java String.trim removes code units at most U+0020 from both ends. -/
def javaTrim (s : String) : String :=
  String.mk (((s.toList.dropWhile (fun c => c.toNat ≤ 32)).reverse.dropWhile
    (fun c => c.toNat ≤ 32)).reverse)

/-- A Java String value is its ordered UTF-16 code units, including lone surrogates. -/
abbrev JavaString := List UInt16

def scalar (u : UInt16) : Nat :=
  if u.toNat ≤ 32 then u.toNat else 65536 + u.toNat

def unit (u : UInt16) : Char := Char.ofNat (scalar u)
def nonnull (s : JavaString) : String := String.mk (s.map unit)
def nullMarker : String := String.mk [Char.ofNat 33]
def nullable : Option JavaString → String
  | none => nullMarker
  | some s => nonnull s

def trimUnits (s : JavaString) : JavaString :=
  ((s.dropWhile (fun u => u.toNat ≤ 32)).reverse.dropWhile
    (fun u => u.toNat ≤ 32)).reverse

/-- Only raw record values; this is not a Java API or an execution model. -/
structure RawRecord where
  id : Option JavaString
  accumulator : Option JavaString
  version : Int
  created : Option JavaString
  updated : Option JavaString
  deriving DecidableEq

def image (r : RawRecord) : Image :=
  ⟨nullable r.id, nullable r.accumulator, r.version, nullable r.created, nullable r.updated⟩

def updateRaw (r : RawRecord) (a t : JavaString) : RawRecord :=
  { r with accumulator := some a, version := r.version + 1, updated := some t }

-- Frozen theorem signatures. Each implementation is checked against this type.
def UnitValidSpec : Prop := ∀ u, Char.isValidCharNat (scalar u)
def UnitCodeSpec : Prop := ∀ u, (unit u).toNat = scalar u
def UnitInjectiveSpec : Prop := ∀ a b, unit a = unit b → a = b
def SentinelSpec : Prop := ∀ u, unit u ≠ Char.ofNat 33
def NonnullInjectiveSpec : Prop := ∀ a b, nonnull a = nonnull b → a = b
def NullableInjectiveSpec : Prop := ∀ a b, nullable a = nullable b → a = b
def EmptySpec : Prop := ∀ s, nonnull s = "" ↔ s = []
def NonemptySpec : Prop := ∀ s, nonnull s ≠ "" ↔ s ≠ []
def EqualitySpec : Prop := ∀ a b, nonnull a = nonnull b ↔ a = b
def NullableEqualitySpec : Prop := ∀ a b, nullable a = nullable b ↔ a = b
def LengthSpec : Prop := ∀ s, (nonnull s).length = s.length
def NullDistinctSpec : Prop := ∀ s, nullable none ≠ nonnull s
def TrimSpec : Prop := ∀ s, javaTrim (nonnull s) = nonnull (trimUnits s)
def NormalizedSpec : Prop := ∀ s,
  javaTrim (nonnull s) = nonnull s ↔ trimUnits s = s
def TrimNonemptySpec : Prop := ∀ s,
  javaTrim (nonnull s) ≠ "" ↔ trimUnits s ≠ []
def ImageInjectiveSpec : Prop := ∀ a b, image a = image b → a = b
def FieldsSpec : Prop := ∀ r,
  (image r).id = nullable r.id ∧ (image r).accumulator = nullable r.accumulator ∧
  (image r).version = r.version ∧ (image r).created = nullable r.created ∧
  (image r).updated = nullable r.updated
def IncrementSpec : Prop := ∀ r a t,
  image (updateRaw r a t) =
    { image r with accumulator := nonnull a, version := r.version + 1, updated := nonnull t }

end Argos.JavaValues

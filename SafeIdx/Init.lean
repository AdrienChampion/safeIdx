/-! # Basic definitions -/



namespace SafeIdx

/-- The `𝕂`onstant combinator. -/
def 𝕂 (val : α) : β → α :=
  fun _ => val



/-- Specification for a type-safe index.

This tells this library how to go from `Nat` to the index type and `Back`, and also requires that
the composition of the two is the identity, *i.e.* they *cancel* each other.
-/
class UidSpec (α : Type) where
  /-- Extracts the actual index. -/
  toNat : α → Nat
  /-- Uid constructor. -/
  ofNat : Nat → α
  /-- `ofNat` cancels `toNat`. -/
  cancel_of_to : ofNat (toNat a) = a
  /-- `toNat` cancels `toNat`. -/
  cancel_to_of : toNat (ofNat n) = n

open UidSpec (toNat ofNat)



section fuid
  /-- A uid with an upper-bound, coerces to its `Uid` type parameter.

  This type is a generalized version of Lean core's `Fin`. Unlike `Fin` which specifies that a `Nat`
  (often seen as an array-index) is strictly smaller than some value `n` (`Fin n`), `FUid` is
  parameterized by the index type in addition to the `Nat` upper-bound: `Fin Uid n`.

  The actual upper-bound is a `Nat` and not a `Uid`-value since it will correspond to the length of
  an array, just like `Fin`. Since we don't want to create `Uid` values that are not legal indices
  for the array they come from, it would be bad form to have the upper-bound be a `Uid` that's not
  legal for that array since it corresponds to its length.
  -/
  structure FUid
    (Uid : Type) [UidSpec Uid]
    (n : Nat)
  where
    uid : Uid
    isLt : toNat uid < n := by simp_arith

  instance FUid.toString
    [UidSpec Uid] [ToString Uid]
  : ToString (FUid Uid n) where
    toString fuid :=
      s!"{fuid.uid}<{n}"

  variable
    {Uid : Type}
    [UidSpec Uid]
    {n : Nat}

  instance : CoeDep (FUid Uid n) fuid Uid where
    coe := fuid.uid

  /-- A `FUid _ n'` is a `FUid _ n` when `n' ≤ n`. -/
  def FUid.lift
    (fuid : FUid Uid n')
    (h : n' ≤ n := by try assumption ; try simp_arith)
  : FUid Uid n :=
    ⟨fuid.uid, Nat.lt_of_lt_of_le fuid.isLt h⟩

  /-- Turns a `Nat` into a `FUid n`. -/
  def FUid.ofNat
    {Uid : outParam Type} [S : UidSpec Uid]
    (n n' : Nat)
    (h : n' < n := by simp_arith)
  : FUid Uid n :=
    ⟨S.ofNat n', by simp [S.cancel_to_of] ; assumption⟩

  /-- A `n`-`FUid` is also a `n+1`-`FUid`. -/
  def FUid.inc
    (fuid : FUid Uid n)
  : FUid Uid (n + 1) :=
    ⟨
      fuid, by
        let h := fuid.isLt
        simp_arith
        exact Nat.le_of_lt h
    ⟩

  /-- Applies `f` taking `n+1`-`FUid`-s, and applies it to a `n`-`FUid`. -/
  def FUid.applyInc
    (f : FUid Uid (n + 1) → α)
    (fuid : FUid Uid n)
  : α :=
    f fuid.inc
end fuid

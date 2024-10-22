import SafeIdx.Map.UidMapD
import SafeIdx.Map.UidMap



/-! # Extra mapping features -/
namespace SafeIdx



/-! ## Iterating over indices -/
section indices

/-- A range over the `Uid`s for some map. -/
structure Range (Uid : Type) [UidSpec Uid] (n : Nat) where
  /-- Underlying range. -/
  raw : Std.Range
  /-- Link between `raw` and the `n` parameter. -/
  inv_stop : n = raw.stop


variable
  {Uid : Type} [S : UidSpec Uid]
  {β : Type u}
  {m : Type u → Type u} [Monad m]



/-- For-loop handling, used to instantiate `ForIn`. -/
protected def Range.forIn
  (range : Range Uid n)
  (b : β)
  (f : FUid Uid n → β → m (ForInStep β))
: m β := do
  let mut acc := b
  for h : idx in range.raw do
    let fuid : FUid Uid n :=
      FUid.mk
        (S.ofNat idx)
        (range.inv_stop ▸ S.cancel_to_of ▸ h.upper)
    match ← f fuid acc with
    | .done res =>
      acc := res
      break
    | .yield res =>
      acc := res
  return acc

instance : ForIn m (Range Uid n) (FUid Uid n) where
  forIn := Range.forIn



/-- Range over the indices of `_uidMapD`. -/
def UidMapD.indices (_uidMapD : UidMapD n Uid α) : Range Uid n where
  raw := [:n]
  inv_stop := rfl

/-- Range over the indices of `map`. -/
def UidMap.indices (uidMap : UidMap Uid α) : Range Uid uidMap.len where
  raw := [:uidMap.len]
  inv_stop := rfl

end indices



/-! ## Iterating on elements -/
section iter

variable
  {Uid : Type} [S : UidSpec Uid]
  {n : Nat}


/-- For-loop handling, used to instantiate `ForIn`. -/
protected def UidMapD.forInIdx
  {α : Type u} {β : Type v}
  {m : Type v → Type w} [Monad m]
  (uidMap : UidMapD n Uid α)
  (b : β)
  (f : FUid Uid n × α → β → m (ForInStep β))
: m β := do
  let mut acc := b
  for h : idx in [:n] do
    let fuid : FUid Uid n :=
      FUid.mk (S.ofNat idx) (S.cancel_to_of ▸ h.upper)
    let val :=
      uidMap.get fuid
    match ← f (fuid, val) acc with
    | .done res =>
      acc := res
      break
    | .yield res =>
      acc := res
  return acc

/-- For-loop handling, used to instantiate `ForIn`. -/
protected def UidMapD.forIn
  {α : Type u} {β : Type v}
  {m : Type v → Type w} [Monad m]
  (uidMap : UidMapD n Uid α)
  (b : β)
  (f : α → β → m (ForInStep β))
: m β := do
  uidMap.forInIdx b fun (_idx, a) => f a

/-- Defeq `UidMapD`: this type instantiates `ForIn` over `FUid`s only.

Constructed using `UidMapD.iterIdx` and `UidMap.iterIdx`.
-/
protected def IterIdx
  (len : Nat)
  (Uid : Type)
  [UidSpec Uid]
  (α : Type u)
:=
  UidMapD len Uid α

/-- Transforms a `UidMapD` in an `IterIdx` allowing to iterate on indices only.

Value-wise, this function is the identity as `IterIdx` defeq `UidMapD`.
-/
def UidMapD.iterIdx
  (uidMap : UidMapD n Uid α)
: SafeIdx.IterIdx n Uid α :=
  uidMap

/-- Transforms a `UidMap` in an `IterIdx` allowing to iterate on indices only.

Value-wise, this function is just the `UidMap.dmap` projection as `IterIdx` defeq `UidMapD`.
-/
def UidMap.iterIdx
  (uidMap : UidMap Uid α)
: SafeIdx.IterIdx uidMap.len Uid α :=
  uidMap.dmap.iterIdx

instance : ForIn m (UidMapD n Uid α) α where
  forIn := UidMapD.forIn

instance : ForIn m (UidMap Uid α) α where
  forIn map := map.dmap.forIn

instance : ForIn m (SafeIdx.IterIdx n Uid α) (FUid Uid n × α) where
  forIn := UidMapD.forInIdx

end iter

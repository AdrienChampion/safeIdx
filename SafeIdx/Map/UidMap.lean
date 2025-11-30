import SafeIdx.Map.UidMapD



/-! # Mapping from uid-s to some type

`UidMap` is a thin wrapper around `UidMapD`.
-/
namespace SafeIdx

open UidSpec (ofNat toNat)



/-- A map from `Uid` to `α`, built on top of `UidMapD`. -/
structure UidMap
  (Uid : Type) [UidSpec Uid]
  (α : Type)
where
  len : Nat
  dmap : UidMapD len Uid α
deriving Repr, Inhabited, Hashable



variable
  {Uid : Type}
  [UidSpec Uid]
  {α : Type}
  (uidMap : UidMap Uid α)
  (uid : Uid)



/-- True if `id` is a legal index for `uidMap` (decidable). -/
@[simp]
def UidMap.isLegal : Prop :=
  toNat uid < uidMap.len

instance : Decidable (uidMap.isLegal uid) := by
  simp only [UidMap.isLegal]
  exact inferInstance

/-- Turns a legal uid for a map into a `FUid` smaller than the map's length. -/
def FUid.ofLegal
  {uidMap : UidMap Uid α} {uid : Uid}
  (h: uidMap.isLegal uid)
: FUid Uid uidMap.len :=
  ⟨uid, h⟩

/-- A `FUid _ n` is a legal index for `map` if `n` is smaller than `map`'s length. -/
@[simp]
def FUid.mapLift
  (fuid : FUid Uid n)
  {map : outParam $ UidMap Uid α}
  (h : n ≤ map.len := by try simp ; assumption)
: FUid Uid map.len :=
  fuid.lift



section

variable (uidMap : UidMap Uid α)

/-- Size/length of a map. -/
def UidMap.length : Nat :=
  uidMap.len
/-- Size/length of a map. -/
def UidMap.size : Nat :=
  uidMap.len

/-- Produces a list of all the elements. -/
def UidMap.toList : List α :=
  uidMap.dmap.toList

end



@[inherit_doc UidMapD.mkEmpty]
def UidMap.mkEmpty
  {α : outParam Type}
  (capacity : Nat := 666)
: UidMap Uid α :=
  ⟨0, UidMapD.mkEmpty capacity⟩

@[simp]
theorem UidMap.mkEmpty_len
  {α : outParam Type}
: (mkEmpty capacity : UidMap Uid α).len = 0 := rfl

@[inherit_doc UidMapD.generate]
def UidMap.generate
  (len : Nat)
  (gen : FUid Uid len → α)
  (capacity : Nat := 666)
: UidMap Uid α :=
  ⟨len, UidMapD.generate len gen capacity⟩

@[inherit_doc UidMapD.mkD]
def UidMap.mkD
  (len : Nat)
  (default : α)
  (capacity : Nat := 666)
: UidMap Uid α :=
  generate len (𝕂 default) capacity
@[inherit_doc UidMapD.mkI]
def UidMap.mkI
  (len : Nat)
  [Inhabited α]
  (capacity : Nat := 666)
: UidMap Uid α :=
  mkD len default capacity



@[inherit_doc UidMapD.pushIdx]
def UidMap.pushIdx
  (gen : FUid Uid (uidMap.len + 1) → α)
: FUid Uid (uidMap.len + 1) × UidMap Uid α :=
  let (uid, dmap) := uidMap.dmap.pushIdx gen
  (uid, ⟨uidMap.len + 1, dmap⟩)
@[inherit_doc UidMapD.pushIdx']
def UidMap.pushIdx'
  (gen : FUid Uid (uidMap.len + 1) → α)
: UidMap Uid α :=
  uidMap.pushIdx gen |>.2
@[inherit_doc UidMapD.push]
def UidMap.push
  (a : α)
: FUid Uid (uidMap.len + 1) × UidMap Uid α :=
  uidMap.pushIdx (𝕂 a)
@[inherit_doc UidMapD.push']
def UidMap.push'
  (a : α)
: UidMap Uid α :=
  uidMap.push a |>.2

section

variable
  {uidMap : UidMap Uid α}
  {gen : FUid Uid (uidMap.len + 1) → α}
  {val : α}

@[simp]
theorem Map.pushIdx_len : (uidMap.pushIdx gen).2.len = uidMap.len + 1 :=
  rfl
@[simp]
theorem Map.pushIdx'_len : (uidMap.pushIdx' gen).len = uidMap.len + 1 :=
  rfl
@[simp]
theorem Map.push_len : (uidMap.push val).2.len = uidMap.len + 1 :=
  rfl
@[simp]
theorem Map.push'_len : (uidMap.push' val).len = uidMap.len + 1 :=
  rfl

end



@[inherit_doc UidMapD.get]
def UidMap.get
  (fuid : FUid Uid uidMap.len)
: α :=
  uidMap.dmap.get fuid

/-- `Uid` array-access notation for `Map`s. -/
instance : GetElem
  (UidMap Uid α) Uid α
  (·.isLegal ·)
where
  getElem dmap _uid legal :=
    FUid.ofLegal legal
    |> dmap.get

/-- `FUid` array-access notation for `Map`s. -/
instance : GetElem
  (UidMap Uid α) (FUid Uid n) α
  fun map _uid => n ≤ map.len
where
  getElem dmap fuid h :=
    dmap.get fuid.lift

@[inherit_doc UidMapD.get?]
def UidMap.get? : Uid → Option α :=
  uidMap.dmap.get?
@[inherit_doc UidMapD.get!]
def UidMap.get! : Uid → [Inhabited α] → α :=
  uidMap.dmap.get!
@[inherit_doc UidMapD.getD]
def UidMap.getD : Uid → α  → α :=
  uidMap.dmap.getD
@[inherit_doc UidMapD.getI]
def UidMap.getI : Uid → [Inhabited α] → α :=
  uidMap.dmap.getI



section set

variable
  (fuid : FUid Uid uidMap.len)
  (a : α)

@[inherit_doc UidMapD.set]
def UidMap.set : UidMap Uid α :=
  {uidMap with dmap := uidMap.dmap.set fuid a}
@[inherit_doc UidMapD.set?]
def UidMap.set? : Bool × UidMap Uid α :=
  let (flag, dmap) :=
    uidMap.dmap.set? uid a
  (flag, {uidMap with dmap})
@[inherit_doc UidMapD.set!]
def UidMap.set! [Inhabited α] : UidMap Uid α :=
  {uidMap with dmap := uidMap.dmap.set! uid a}

end set



def UidMap.mapValueM
  {M : Type → Type} [Monad M]
  (uid : Uid) (h : uidMap.isLegal uid) (f : α → M (α × β))
: M (β × UidMap Uid α) := do
  let (res, dmap) ← uidMap.dmap.mapValueM ⟨uid, h⟩ f
  return (res, {uidMap with dmap})

def UidMap.mapValue
  (uid : Uid) (h : uidMap.isLegal uid) (f : α → α × β)
: β × UidMap Uid α :=
  uidMap.mapValueM (M := Id) uid h f

def UidMap.mapValue?
  (uid : Uid) (fLegal : α → α × β) (fElse : Unit → β)
: β × UidMap Uid α :=
  if h : uidMap.dmap.isLegal uid then
    uidMap.mapValue uid h fLegal
  else
    (fElse (), uidMap)

def UidMap.mapValue!
  [Inhabited α] [Inhabited β] [ToString Uid]
  (uid : Uid) (fLegal : α → α × β)
: β × UidMap Uid α :=
  if h : uidMap.dmap.isLegal uid then
    uidMap.mapValue uid h fLegal
  else
    panic!
      s!"illegal index `{uid}` for a map containing {uidMap.len} element(s)"



section fold

/-- Fold-left with element indices. -/
def UidMap.foldlIdx
  (f : β → FUid Uid uidMap.len → α → β )
  (init : β)
: β :=
  uidMap.dmap.foldlIdx f init

/-- Fold-left, see also `foldlIdx`. -/
def UidMap.foldl
  (f : β → α → β)
  (init : β)
: β :=
  uidMap.foldlIdx (fun acc _ => f acc) init



/-- Fold-right with element indices. -/
def UidMap.foldrIdx
  (f : FUid Uid uidMap.len → α → β → β )
  (init : β)
: β :=
  uidMap.dmap.foldrIdx f init

/-- Fold-right, see also `foldrIdx`. -/
def UidMap.foldr
  (f : α → β → β)
  (init : β)
: β :=
  uidMap.foldrIdx (𝕂 f) init

end fold




section pure

/-- Constructs the map with only one mapping: first uid to `a`. -/
def UidMap.pure (a : α) : UidMap Uid α :=
  ⟨1, UidMapD.pure a⟩

instance : Pure (UidMap Uid) where
  pure := UidMap.pure

end pure



section map

/-- Turns a map to `α`-values into a map to `β`-values. -/
def UidMap.mapIdx
  (map : UidMap Uid α)
  (f : FUid Uid map.len → α → β)
  (capacity : Nat := map.len)
: UidMap Uid β :=
  generate map.len (fun id => f id $ map.get id) capacity

/-- Plain map operation, does not give access to indices. -/
def UidMap.map
  (f : α → β)
  (map : UidMap Uid α)
: UidMap Uid β :=
  ⟨map.len, map.dmap.map f⟩

/-- `UidMapD` is a functor. -/
instance : Functor (UidMap Uid) where
  map := UidMap.map

end map



section applicative

/-- Eager version of monadic `seq`. -/
def UidMap.seqE
  (fnMap : UidMap Uid (α → β))
  (uidMap : UidMap Uid α)
  (legal : fnMap.len = uidMap.len)
: UidMap Uid β :=
  generate fnMap.len
    (fun uid => (fnMap.get uid) (uidMap.get (legal ▸ uid)))

/-- Lazy version of monadic `seq`. -/
def UidMap.seq
  (fnMap : UidMap Uid (α → β))
  (uidMap : Unit → UidMap Uid α)
  (legal : fnMap.len = (uidMap ()).len)
: UidMap Uid β :=
  let uidMap := uidMap ()
  generate uidMap.len
    (fun id => (fnMap.get (legal ▸ id)) (uidMap.get id))



-- /-- `UidMapD` is an applicative. -/
-- instance : Applicative (UidMap Uid) where
--   seq fnMap uidMap :=
--     let uidMap' := uidMap ()
--     if legal : fnMap.len = uidMap'.len
--     then fnMap.seq uidMap legal
--     else .mkEmpty

end applicative



section conv

/-- Turns a `UidMapD` into a `Map`. -/
abbrev UidMapD.toMap
  (dmap : UidMapD n Uid α)
: UidMap Uid α :=
  ⟨n, dmap⟩

@[simp]
theorem UidMapD.toMap_len
  {dmap : UidMapD n Uid α}
  {map : UidMap Uid α}
  (h : map = dmap.toMap)
: map.len = n := by
  simp only [h, toMap]

/-- Turn a `UidMapD` into a `Map`. -/
abbrev Map.ofUidMapD :=
  @UidMapD.toMap

@[simp]
theorem Map.ofUidMapD_len
  {dmap : UidMapD n Uid α}
  {map : UidMap Uid α}
  (h : map = Map.ofUidMapD dmap)
: map.len = n :=
  UidMapD.toMap_len h



/-- Turns a `Map` into a `UidMapD`. -/
abbrev Map.toUidMapD
  (map : UidMap Uid α)
: UidMapD map.len Uid α :=
  map.dmap

/-- Turns a `Map` into a `UidMapD`. -/
abbrev UidMapD.ofMap :=
  @Map.toUidMapD

end conv

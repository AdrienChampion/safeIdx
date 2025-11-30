import SafeIdx.Init



/-! # Dependent mapping from uid-s to values of some type

`UidMapD` is parameterized by the size of the mapping, unlike the other mapping type provided by
this library, `Map`, which is just a thin wrapper around `UidMapD`.
-/
namespace SafeIdx

open UidSpec (toNat ofNat)



/-- A dependent map from `Uid` to `α` of length `n`. -/
structure UidMapD
  (n : Nat)
  (Uid : Type)
  [S : UidSpec Uid]
  (α : Type u)
where private _mk ::
  /-- Underlying array, never accessed directly by users. -/
  private raw : Array α
  /-- `n` is actually the size of `raw`. -/
  private len_inv : raw.size = n
deriving Repr, DecidableEq, Hashable




section

variable
  {n : Nat}
  {Uid : Type}
  [S : UidSpec Uid]
  {α : Type u}
  (dmap : UidMapD n Uid α)
  (uid : Uid)



@[simp]
theorem UidMapD.invariant : dmap.raw.size = n :=
  dmap.len_inv



/-- True if `id` is a legal index for `map` (decidable). -/
@[simp]
def UidMapD.isLegal : Prop :=
  let _ := dmap -- force `dmap` as a parameter of this def
  toNat uid < n

@[simp]
private theorem UidMapD.legalIndex_of_isLegal
  {dmap : UidMapD n Uid α} {id : Uid}
:
  dmap.isLegal id → toNat id < dmap.raw.size
:= by
  simp only [isLegal, invariant]
  exact (·)

instance : Decidable (dmap.isLegal uid) := by
  simp only [UidMapD.isLegal]
  exact inferInstance



/-- Constructor from a legal uid. -/
def FUid.ofDLegal
  {dmap : UidMapD n Uid α} {uid : Uid}
  (h: dmap.isLegal uid)
: FUid Uid n :=
  ⟨uid, h⟩



/-- Size/length of a map. -/
def UidMapD.len : Nat :=
  let _ := dmap -- force `dmap` as a parameter of this def
  n
/-- Size/length of a map. -/
def UidMapD.length : Nat :=
  dmap.len
/-- Size/length of a map. -/
def UidMapD.size : Nat :=
  dmap.len

/-- Produces a list of all the elements. -/
def UidMapD.toList : List α :=
  dmap.raw.toList



/-- Creates an empty map with some capacity. -/
def UidMapD.mkEmpty
  {α : outParam $ Type u}
  (capacity : Nat := 666)
: UidMapD 0 Uid α :=
  ⟨Array.mkEmpty capacity, rfl⟩



/-- Pushes an element using a `gen`erator and yields its index. -/
def UidMapD.pushIdx (gen : FUid Uid (n + 1) → α) : FUid Uid (n + 1) × UidMapD (n + 1) Uid α :=
  let fuid := FUid.ofNat (n + 1) n
  (fuid, ⟨dmap.raw.push (gen fuid), by simp⟩)
/-- Pushes an element using a `gen`erator. -/
def UidMapD.pushIdx' (gen : FUid Uid (n + 1) → α) : UidMapD (n + 1) Uid α :=
  dmap.pushIdx gen |>.2
/-- Pushes an element at the end of the map and yields the element's index. -/
def UidMapD.push (a : α) : FUid Uid (n + 1) × UidMapD (n + 1) Uid α :=
  dmap.pushIdx fun _ => a
/-- Pushes an element at the end of the map. -/
def UidMapD.push' (a : α) : UidMapD (n + 1) Uid α :=
  dmap.push a |>.2



/-- Populates a map of length `n` using a `gen`erator. -/
def UidMapD.generate
  (n : Nat)
  (gen : FUid Uid n → α)
  (capacity : Nat := 666)
: UidMapD n Uid α :=
  match n with
  | 0 =>
    mkEmpty capacity
  | n' + 1 =>
    let genInc :=
      FUid.applyInc gen
    generate n' genInc capacity
    |>.pushIdx' gen

/-- Generates a map containing `n` elements all equal to `default`. -/
def UidMapD.mkD
  (n : Nat)
  (default : α)
  (capacity : Nat := 666)
: UidMapD n Uid α :=
  generate n (fun _ => default) capacity

/-- Generates a map containing `n` elements all equal to `Inhabited.default`. -/
def UidMapD.mkI
  (n : Nat)
  [Inhabited α]
  (capacity : Nat := 666)
: UidMapD n Uid α :=
  generate n (fun _ => default) capacity

instance : Inhabited (UidMapD 0 Uid α) where
  default :=
    UidMapD.mkEmpty

instance [Inhabited α] : Inhabited (UidMapD n Uid α) where
  default :=
    UidMapD.mkI n



/-- Same as `get` but takes a `FUid` uid. -/
def UidMapD.get (fuid : FUid Uid n) : α :=
  let h : toNat fuid.uid < dmap.raw.size :=
    by simp [fuid.isLt]
  dmap.raw[toNat fuid.uid]

/-- `Uid` array-access notation for `UidMapD`s. -/
instance : GetElem
  (UidMapD n Uid α) Uid α
  (·.isLegal ·)
where
  getElem dmap _uid legal :=
    FUid.ofDLegal legal
    |> dmap.get

/-- `FUid` array-access notation for `UidMapD`s. -/
instance : GetElem
  (UidMapD n Uid α) (FUid Uid n) α $ 𝕂 (𝕂 True)
where
  getElem dmap fuid _ :=
    dmap.get fuid

/-- `FUid` array-access notation for `UidMapD`s, different-length version. -/
instance : GetElem
  (UidMapD n Uid α) (FUid Uid n') α fun _ _ => n' ≤ n
where
  getElem dmap fuid h :=
    dmap.get fuid.lift

/-- Attempts to retrieve a value in the map. -/
def UidMapD.get? : Option α :=
  dmap.raw[toNat uid]?

/-- Retrieves a value at some index, crashes if none. -/
def UidMapD.get! [Inhabited α] : α :=
  if h : dmap.isLegal uid
  then dmap[uid]
  else panic! s!"illegal uid-index `{toNat uid}`, length is `{n}`"

/-- Retrieves a value at some index, yields a default value if none. -/
def UidMapD.getD (default : α) : α :=
  dmap.raw.getD (toNat uid) default

/-- Retrieves a value at some index, yields a default value from `Inhabited` if none. -/
def UidMapD.getI [Inhabited α] : α :=
  if let some a := dmap.get? uid
  then a else default



section set

variable
  (fuid : FUid Uid n)
  (a : α)

/-- Sets a value in the map. -/
def UidMapD.set : UidMapD n Uid α :=
  ⟨dmap.raw.set (toNat fuid.uid) a (legalIndex_of_isLegal fuid.isLt), by simp⟩

/-- Attempts to set a value in the map, yields `true` if successful. -/
def UidMapD.set? : Bool × UidMapD n Uid α :=
  if h : dmap.isLegal uid
  then (true, dmap.set ⟨uid, h⟩ a)
  else (false, dmap)

/-- Attempts to set a value in the map, crashes on failure. -/
def UidMapD.set! [Inhabited α] : UidMapD n Uid α :=
  if h : dmap.isLegal uid
  then dmap.set ⟨uid, h⟩ a
  else panic! s!"illegal index {S.toNat uid}, length is {n}"

end set



def UidMapD.mapValueM
  {β : Type u}
  {M : Type u → Type v} [Monad M]
  (uid : FUid Uid n) (f : α → M (α × β))
: M (β × UidMapD n Uid α) := do
  let (val, res) ← f $ dmap.get uid
  return (res, dmap.set uid val)



section fold

/-- Fold-left with element indices. -/
def UidMapD.foldlIdx
  (dmap : UidMapD n Uid α)
  (f : β → FUid Uid n → α → β )
  (init : β)
: β :=
  foldlIdxAux init 0
where
  foldlIdxAux (acc : β) (idx : Nat) :=
    if h : idx < n then
      let fuid : FUid Uid n :=
        FUid.mk (ofNat idx) $ S.cancel_to_of ▸ h
      let acc := f acc fuid dmap[fuid]
      foldlIdxAux acc idx.succ
    else
      acc
  termination_by n - idx
  decreasing_by
    simp_wf
    apply Nat.sub_lt_sub_left
    · exact h
    · exact Nat.lt_succ_self idx

/-- Fold-left, see also `foldlIdx`. -/
def UidMapD.foldl
  (f : β → α → β)
  (init : β)
: β :=
  dmap.foldlIdx (fun acc => 𝕂 $ f acc) init



/-- Fold-right with element indices. -/
def UidMapD.foldrIdx
  (f : FUid Uid n → α → β → β )
  (init : β)
: β :=
  foldrIdxAux init n
where
  foldrIdxAux
    (acc : β) (idxSucc : Nat)
    (h : idxSucc ≤ n := by grind)
  := match idxSucc with
  | 0 => acc
  | idx + 1 =>
    if h : idx < n then
      let fuid : FUid Uid n :=
        FUid.mk (ofNat idx) $ S.cancel_to_of ▸ h
      let acc := f fuid dmap[fuid] acc
      foldrIdxAux acc idx $ Nat.le_of_lt h
    else
      acc

/-- Fold-right, see also `foldrIdx`. -/
def UidMapD.foldr
  (f : α → β → β)
  (init : β)
: β :=
  dmap.foldrIdx (𝕂 f) init

end fold



/-- Merges the bindings from two maps. -/
def UidMapD.merge
  (dmap' : UidMapD n Uid β)
  (f : FUid Uid n → α → β → γ)
: UidMapD n Uid γ :=
  generate n fun fuid => f fuid dmap[fuid] dmap'[fuid]

/-- Zips two maps. -/
def UidMapD.zip
  (dmap' : UidMapD n Uid β)
: UidMapD n Uid (α × β) :=
  dmap.merge dmap' $ 𝕂 Prod.mk



section pure

/-- Builds a map of length `n` with all cells storing `a`. -/
def UidMapD.pure
  {n : outParam Nat}
  (a : α)
: UidMapD n Uid α :=
  UidMapD.mkD n a

instance : Pure (UidMapD n Uid) where
  pure := UidMapD.pure

end pure

section map

/-- Turns a map to `α`-values into a map to `β`-values. -/
def UidMapD.mapIdx
  (f : FUid Uid n → α → β)
  (dmap : UidMapD n Uid α)
: UidMapD n Uid β :=
  generate n (fun id => f id $ dmap.get id)

/-- Plain map operation, does not give access to indices. -/
def UidMapD.map
  (f : α → β)
  (dmap : UidMapD n Uid α)
: UidMapD n Uid β :=
  dmap.mapIdx (𝕂 f)

/-- `UidMapD` is a functor. -/
instance : Functor (UidMapD n Uid) where
  map := UidMapD.map

end map



section applicative

/-- Eager version of monadic `seq`. -/
def UidMapD.seqE
  (fnMap : UidMapD n Uid (α → β))
  (dmap : UidMapD n Uid α)
: UidMapD n Uid β :=
  generate n
    (fun uid => (fnMap.get uid) (dmap.get uid))

/-- Lazy version of monadic `seq`. -/
def UidMapD.seq
  (fnMap : UidMapD n Uid (α → β))
  (dmap : Unit → UidMapD n Uid α)
: UidMapD n Uid β :=
  let dmap := dmap ()
  generate n
    (fun id => (fnMap.get id) (dmap.get id))



/-- `UidMapD` is an applicative. -/
instance : Applicative (UidMapD n Uid) where
  seq := UidMapD.seq

end applicative

end

import Lean.Elab.Command

import SafeIdx.Map



namespace SafeIdx.Dsl

open Lean Elab Command Term Meta



section
  protected def mapRedefs
    (mods : TSyntax `Lean.Parser.Command.declModifiers)
    (idxIdent : Ident)
    (instIdent : Ident)
    (fuidIdent : Ident)
    (mapIdent : Ident)
    (isDependent : Bool)
  := do
    -- identifiers we're gonna use in codegen
    let capa := mkIdent `capacity
    let alpha := mkIdent `α
    let len := mkIdent `len
    let gen := mkIdent `gen

    if isDependent then
      elabCommand $ ← `(
        $mods:declModifiers
        def $mapIdent ($len:ident : Nat) ($alpha:ident : Type) :=
          @SafeIdx.UidMapD $len $idxIdent $instIdent $alpha
        namespace $mapIdent
          @[inherit_doc SafeIdx.UidMapD.mkEmpty]
          abbrev $(mkIdent `mkEmpty)
            {$alpha : Type}
            ($capa : Nat := 666)
          : $mapIdent 0 $alpha :=
            SafeIdx.UidMapD.mkEmpty $capa
          @[inherit_doc SafeIdx.UidMapD.generate]
          abbrev $(mkIdent `generate)
            ($len:ident : Nat)
            ($gen : $fuidIdent $len → $alpha)
            ($capa : Nat := 666)
          : $mapIdent $len $alpha :=
            SafeIdx.UidMapD.generate $len $gen $capa
          @[inherit_doc SafeIdx.UidMapD.mkD]
          abbrev $(mkIdent `mkD)
            ($len:ident : Nat)
            (default : $alpha)
            ($capa : Nat := 666)
          : $mapIdent $len $alpha :=
            SafeIdx.UidMapD.mkD $len default $capa
          @[inherit_doc SafeIdx.UidMapD.mkI]
          abbrev $(mkIdent `mkI)
            ($len:ident : Nat)
            [Inhabited $alpha]
            ($capa : Nat := 666)
          : $mapIdent $len $alpha :=
            SafeIdx.UidMapD.mkI $len $capa
        end $mapIdent
      )
    else
      elabCommand $ ← `(
        $mods:declModifiers
        def $mapIdent ($alpha:ident : Type) :=
          @SafeIdx.UidMap $idxIdent $instIdent $alpha
        namespace $mapIdent
          @[inherit_doc SafeIdx.UidMap.mkEmpty]
          abbrev $(mkIdent `mkEmpty)
            ($capa : Nat := 666)
          : $mapIdent $alpha :=
            SafeIdx.UidMap.mkEmpty $capa
          @[inherit_doc SafeIdx.UidMap.generate]
          abbrev $(mkIdent `generate)
            ($len:ident : Nat)
            ($gen : $fuidIdent $len → $alpha)
            ($capa : Nat := 666)
          : $mapIdent $alpha :=
            SafeIdx.UidMap.generate $len $gen $capa
          @[inherit_doc SafeIdx.UidMap.mkD]
          abbrev $(mkIdent `mkD)
            ($len:ident : Nat)
            (default : $alpha)
            ($capa : Nat := 666)
          : $mapIdent $alpha :=
            SafeIdx.UidMap.mkD $len default $capa
          @[inherit_doc SafeIdx.UidMap.mkI]
          abbrev $(mkIdent `mkI)
            ($len:ident : Nat)
            [Inhabited $alpha]
            ($capa : Nat := 666)
          : $mapIdent $alpha :=
            SafeIdx.UidMap.mkI $len $capa
        end $mapIdent
      )
end


/-- Defines a safe index type: `index <uid>`.

Note that `<uid>.UidMap α` (`<uid>.UidMapD len α`) is automatically defined as `SafeIdx.UidMap <uid>
α` (`SafeIdx.UidMapD len <uid> α`), but this behavior can be overriden as discussed below.

Also defines `<uid>.FUid n` as `SafeIdx.FUid <uid> n`. `FUid` is a finite `<uid>`, it is the
equivalent of Lean's `Fin`.

### Custom Aliases

The `index` syntax accepts `where` clauses specifying aliases for useful types provided by
`SafeIdx`, most importantly `UidMap` and `UidMapD`.

An alias is of the form `<src> => <ident>` where `<src>` is one of
- `UidMapD`: dependent map from `<uid>` to some `α`, `UidMapD len <uid> α`;
- `UidMap`: map from `<uid>` to some `α`, `UidMap <uid> α`.

For example:

```lean
index Client where
  UidMap => Client.Array
  UidMapD => Client.DArray
```

```lean
index Client where
  UidMap => Clients
  UidMapD => ClientsD
```
-/
syntax (name := SafeIdx.newIndex) declModifiers
  "index " declId
    withPosition(" where "
      (ppLine ppGroup(declModifiers ident " => " ident))*
    )?
: command


@[command_elab SafeIdx.newIndex]
def elabNewIndex : CommandElab
| `(
  $declMods:declModifiers index $idxId
    $[where
      $[$whereMods:declModifiers $whereName:ident => $whereAlias:ident]*
    ]?
) => do
  -- ident version of the type's name, useable as a term unlike `id`
  let idxIdent := Lean.mkIdent idxId.raw[0].getId
  -- name of the `UidSpec` instance
  let instIdent := Lean.mkIdent `instUidSpec
  -- name of the `FUid` specialization
  let fuidIdent :=
    idxId.raw[0].getId.modifyBase (. ++ `FUid)
    |> mkIdentFrom idxId

  -- actual type definition
  elabCommand $ ← `(
    $declMods:declModifiers
    structure $idxId where private mk ::
      private idx : Nat
    deriving Inhabited, Repr

    instance (priority := low) : ToString $idxIdent where
      toString self := s!"#{self.idx}"
  )

  -- register `UidSpec` instance and `FUid` specialization
  elabCommand $ ← `(
    /-- `SafeIdx.UidSpec` mandatory class instantiation. -/
    instance $instIdent:ident : UidSpec $idxIdent :=
      ⟨fun ⟨idx⟩ => idx, (⟨·⟩), rfl, rfl⟩
    
    abbrev $fuidIdent :=
      SafeIdx.FUid $idxIdent
  )

  let mapAliasGen (mods : TSyntax `Lean.Parser.Command.declModifiers) (alias : Lean.Ident) := do
    Dsl.mapRedefs mods idxIdent instIdent fuidIdent alias false
  let dmapAliasGen (mods : TSyntax `Lean.Parser.Command.declModifiers) (alias : Lean.Ident) := do
    Dsl.mapRedefs mods idxIdent instIdent fuidIdent alias true
  -- zip the name and alias arrays together, if any
  let aliasPairs :=
    if
      let (
        some whereName,
        some whereAlias,
        some whereMods
      ) := (whereName, whereAlias, whereMods)
    then (whereName.zip whereAlias).zip whereMods
    else #[]

  let mut hasMapAlias := false
  let mut hasMapDAlias := false
  -- error on unknown name, otherwise alias is appended to the appropriate list
  for ((name, alias), declMods) in aliasPairs do
    match name with
    | `(UidMap) =>
      hasMapAlias := true
      mapAliasGen declMods alias
    | `(UidMapD) =>
      hasMapDAlias := true
      dmapAliasGen declMods alias
    | _ => throwErrorAt name s!"expected `UidMap` or `UidMapD`, found `{name}`"

  -- super ugly trick to construct a `declModifier` for default aliases, super interested in a
  -- cleaner solution
  let doc
    | `($declModifiers:declModifiers structure $ident:declId) =>
      pure declModifiers
    | _ => throwUnsupportedSyntax
  -- generate default aliases if none was provided
  if ¬ hasMapAlias then
    idxId.raw[0].getId.modifyBase (. ++ `UidMap)
    |> mkIdentFrom idxId
    |> mapAliasGen
      ( ← doc (← `(/-- Specialization of `SafeIdx.UidMap`. -/structure Dummy)) )
  if ¬ hasMapDAlias then
    idxId.raw[0].getId.modifyBase (. ++ `UidMapD)
    |> mkIdentFrom idxId
    |> dmapAliasGen
      ( ← doc (← `(/-- Specialization of `SafeIdx.UidMapD`. -/structure Dummy)) )

| _ => throwUnsupportedSyntax

-- /-- Some doc. -/
-- index Blah where
--   UidMap => BlahArray

-- #check BlahArray
-- #check Blah.FUid
-- #check BlahArray.mkEmpty

-- #check Blah.UidMapD
-- #check Blah.UidMapD.generate
-- #check Blah.UidMapD.mkD
-- #check Blah.UidMapD.mkI

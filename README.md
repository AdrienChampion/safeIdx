# SafeIdx

- [Zulip thread][zulip]

A *(type-)safe index* is a type that's a thin wrapper over `Nat` mainly used to (type-)safely access
cells in an array. Safe indices can be seen as **U**nique **ID**entifiers (UIDs) for some type of
data that can be passed around cheaply. Using a dedicated type instead of just `Nat` makes sure we
cannot confuse an index for some data as an index for different data.

Defining a safe index (and a many more useful things, see below) can be done with SafeIdx's `index`
command and is as simple as

```
index MyIndex
```

SafeIdx is currently mostly an exercise for myself (and maybe others). I find safe indexing
libraries to be a great way to get into any language as writing one requires playing around with
types, relatively low-level array manipulations, coercion, custom indexing notation, syntax
extensions, and much more. It should also ideally be zero-cost, so there's even room for messing
around with optimization.

> `<shamelessPlug>`
> 
> In case you're also a Rust user, checkout the Rust version of this library: [`safe_index`] on
> `crates.io`.
>
> `</shamelessPlug>`



## Example

Say you have a `Client` type; SafeIdx can generate a safe index type for it, say `Client.Uid`, along
with a type for mapping `Client.Uid`s to values of some type. This map type is really just an array,
but it can only be indexed by `Client.Uid`. SafeIdx also provides dependent maps where the map's
length appears in the map's type.

If then for some reason you have a `ClientFamily` type and also generate a safe index type for it,
then Lean will prevent you from ever indexing a `Client` map with a `ClientFamily` index and *vice
versa*.

Note that accessing an array uses `Client.FUid`, which is SafeIdx's equivalent of Lean's `Fin` type.
That is, `Client.FUid n` is a `Client.Uid` along with a proof that the UID's internal `Nat` is
strictly smaller than `n`. See the `SafeIdx.FUid` type in [SafeIdx/Map/UidMapD.lean][UidMapD] for
more details.

```lean
-- SafeIdx's syntax extension for defining indices
index Client.Uid

-- map from `Client.Uid` to some type `α`
#check Client.Uid.UidMap
-- Client.Uid.UidMap (α : Type) : Type

-- dependent map from `Client.Uid` to some type `α`
#check Client.Uid.UidMapD
-- Client.Uid.UidMapD (len : Nat) (α : Type) : Type

-- finite UIDs, i.e. UIDs which internal `Nat` value is smaller than `n`
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type
```

Oftentimes we want to rename `UidMap` and `UidMapD`:

```lean
index Client.Uid where
  UidMap => ClientMap
  UidMapD => ClientMapD

#check ClientMap
-- ClientMap (α : Type) : Type
#check ClientMapD
-- ClientMapD (len : Nat) (α : Type) : Type
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type
```

or maybe

```lean
index Client.Uid where
  UidMap => Client.Map
  UidMapD => Client.MapD

#check Client.Map
-- Client.Map (α : Type) : Type
#check Client.MapD
-- Client.MapD (len : Nat) (α : Type) : Type
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type
```

See [`Test/Basic.lean`][testBasic] and [`Test/Client.lean`][testClient] for more details on the
syntax. For more information on mappings (and `FUid`s), see [`SafeIdx.UidMapD`][UidMapD] for
dependent maps and [`SafeIdx.UidMap`][UidMap] for regular ones.

[UidMapD]: SafeIdx/Map/UidMapD.lean
[UidMap]: SafeIdx/Map/UidMap.lean
[testBasic]: SafeIdx/Test/Basic.lean
[testClient]: SafeIdx/Test/Client.lean
[`safe_index`]: https://crates.io/crates/safe_index
[zulip]: https://leanprover.zulipchat.com/#narrow/stream/113489-new-members/topic/SafeIdx.3A.20a.20beginner-friendly.20library
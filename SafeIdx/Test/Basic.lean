import SafeIdx



namespace SafeIdx.Tests



namespace Simple
  index MyIdx

  #check MyIdx.UidMap
  #check MyIdx.FUid
  #check MyIdx.UidMap.mkEmpty

  #check MyIdx.UidMapD
  #check MyIdx.UidMapD.generate
  #check MyIdx.UidMapD.mkD
  #check MyIdx.UidMapD.mkI
end Simple



namespace EmptyWhere
  index MyIdx where

  #check MyIdx.UidMap
  #check MyIdx.FUid
  #check MyIdx.UidMap.mkEmpty

  #check MyIdx.UidMapD
  #check MyIdx.UidMapD.generate
  #check MyIdx.UidMapD.mkD
  #check MyIdx.UidMapD.mkI
end EmptyWhere



namespace RedefMap
  namespace Test₁
    index MyIdx where
      UidMap => Map

    #check Map
    #check MyIdx.FUid
    #check Map.mkEmpty

    #check MyIdx.UidMapD
    #check MyIdx.UidMapD.generate
    #check MyIdx.UidMapD.mkD
    #check MyIdx.UidMapD.mkI
  end Test₁



  namespace Test₂
    index MyIdx where
      UidMap => MyIdx.Map

    #check MyIdx.Map
    #check MyIdx.FUid
    #check MyIdx.Map.mkEmpty

    #check MyIdx.UidMapD
    #check MyIdx.UidMapD.generate
    #check MyIdx.UidMapD.mkD
    #check MyIdx.UidMapD.mkI
  end Test₂
end RedefMap



namespace RedefDMap
  namespace Test₁
    index MyIdx where
      UidMapD => MapD

    #check MyIdx.UidMap
    #check MyIdx.FUid
    #check MyIdx.UidMap.mkEmpty

    #check MapD
    #check MapD.generate
    #check MapD.mkD
    #check MapD.mkI
  end Test₁



  namespace Test₂
    index MyIdx where
      UidMap => MyIdx.Map

    #check MyIdx.Map
    #check MyIdx.FUid
    #check MyIdx.Map.mkEmpty

    #check MyIdx.UidMapD
    #check MyIdx.UidMapD.generate
    #check MyIdx.UidMapD.mkD
    #check MyIdx.UidMapD.mkI
  end Test₂
end RedefDMap



namespace RedefBoth
  namespace Test₁
    index MyIdx where
      UidMap => Map
      UidMapD => MapD

    #check Map
    #check MyIdx.FUid
    #check Map.mkEmpty

    #check MapD
    #check MapD.generate
    #check MapD.mkD
    #check MapD.mkI
  end Test₁



  namespace Test₂
    index MyIdx where
      UidMap => MyIdx.Map
      UidMapD => MyIdx.MapD

    #check MyIdx.Map
    #check MyIdx.FUid
    #check MyIdx.Map.mkEmpty

    #check MyIdx.MapD
    #check MyIdx.MapD.generate
    #check MyIdx.MapD.mkD
    #check MyIdx.MapD.mkI

    -- #eval do
    --   let m := MyIdx.Map.mkEmpty 5
    --   let (idx, m) := m.push 1
    --   let idx : MyIdx := idx.uid
    --   println! "idx : {idx}"
    --   let expr := Lean.ToExpr.toExpr idx
    --   println! "expr : {expr}"
    --   println! "typExpr : {MyIdx.instToExpr.toTypeExpr}"
  end Test₂
end RedefBoth



namespace Readme
  namespace V1
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
  end V1

  namespace V2
    index Client.Uid where
      UidMap => ClientMap
      UidMapD => ClientMapD

    #check ClientMap
    -- ClientMap (α : Type) : Type
    #check ClientMapD
    -- ClientMapD (len : Nat) (α : Type) : Type
    #check Client.Uid.FUid
    -- Client.Uid.FUid (n : Nat) : Type
  end V2

  namespace V3
    index Client.Uid where
      UidMap => Client.Map
      UidMapD => Client.MapD

    #check Client.Map
    -- Client.Map (α : Type) : Type
    #check Client.MapD
    -- Client.MapD (len : Nat) (α : Type) : Type
    #check Client.Uid.FUid
    -- Client.Uid.FUid (n : Nat) : Type
  end V3
end Readme

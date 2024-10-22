import SafeIdx



namespace SafeIdx.Tests



namespace Simple

index MyIdx

#guard_msgs(drop info) in
#check MyIdx.UidMap
#guard_msgs(drop info) in
#check MyIdx.FUid
#guard_msgs(drop info) in
#check MyIdx.UidMap.mkEmpty

#guard_msgs(drop info) in
#check MyIdx.UidMapD
#guard_msgs(drop info) in
#check MyIdx.UidMapD.generate
#guard_msgs(drop info) in
#check MyIdx.UidMapD.mkD
#guard_msgs(drop info) in
#check MyIdx.UidMapD.mkI

end Simple



namespace EmptyWhere

index MyIdx where

#guard_msgs(drop info) in
#check MyIdx.UidMap
#guard_msgs(drop info) in
#check MyIdx.FUid
#guard_msgs(drop info) in
#check MyIdx.UidMap.mkEmpty

#guard_msgs(drop info) in
#check MyIdx.UidMapD
#guard_msgs(drop info) in
#check MyIdx.UidMapD.generate
#guard_msgs(drop info) in
#check MyIdx.UidMapD.mkD
#guard_msgs(drop info) in
#check MyIdx.UidMapD.mkI

end EmptyWhere



namespace RedefMap

namespace Test₁

index MyIdx where
  UidMap => Map

#guard_msgs (drop info) in
#check Map
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check Map.mkEmpty

#guard_msgs (drop info) in
#check MyIdx.UidMapD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.generate
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkI

end Test₁



namespace Test₂

index MyIdx where
  UidMap => MyIdx.Map

#guard_msgs (drop info) in
#check MyIdx.Map
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check MyIdx.Map.mkEmpty

#guard_msgs (drop info) in
#check MyIdx.UidMapD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.generate
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkI

end Test₂

end RedefMap



namespace RedefDMap

namespace Test₁

index MyIdx where
  UidMapD => MapD

#guard_msgs (drop info) in
#check MyIdx.UidMap
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check MyIdx.UidMap.mkEmpty

#guard_msgs (drop info) in
#check MapD
#guard_msgs (drop info) in
#check MapD.generate
#guard_msgs (drop info) in
#check MapD.mkD
#guard_msgs (drop info) in
#check MapD.mkI

end Test₁



namespace Test₂

index MyIdx where
  UidMap => MyIdx.Map

#guard_msgs (drop info) in
#check MyIdx.Map
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check MyIdx.Map.mkEmpty

#guard_msgs (drop info) in
#check MyIdx.UidMapD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.generate
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkD
#guard_msgs (drop info) in
#check MyIdx.UidMapD.mkI

end Test₂

end RedefDMap



namespace RedefBoth

namespace Test₁

index MyIdx where
  UidMap => Map
  UidMapD => MapD

#guard_msgs (drop info) in
#check Map
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check Map.mkEmpty

#guard_msgs (drop info) in
#check MapD
#guard_msgs (drop info) in
#check MapD.generate
#guard_msgs (drop info) in
#check MapD.mkD
#guard_msgs (drop info) in
#check MapD.mkI

end Test₁



namespace Test₂

index MyIdx where
  UidMap => MyIdx.Map
  UidMapD => MyIdx.MapD

#guard_msgs (drop info) in
#check MyIdx.Map
#guard_msgs (drop info) in
#check MyIdx.FUid
#guard_msgs (drop info) in
#check MyIdx.Map.mkEmpty

#guard_msgs (drop info) in
#check MyIdx.MapD
#guard_msgs (drop info) in
#check MyIdx.MapD.generate
#guard_msgs (drop info) in
#check MyIdx.MapD.mkD
#guard_msgs (drop info) in
#check MyIdx.MapD.mkI

end Test₂
end RedefBoth



namespace Readme

namespace V1

-- SafeIdx's syntax extension for defining indices
index Client.Uid

-- map from `Client.Uid` to some type `α`
#guard_msgs (drop info) in
#check Client.Uid.UidMap
-- Client.Uid.UidMap (α : Type) : Type

-- dependent map from `Client.Uid` to some type `α`
#guard_msgs (drop info) in
#check Client.Uid.UidMapD
-- Client.Uid.UidMapD (len : Nat) (α : Type) : Type

-- finite UIDs, i.e. UIDs which internal `Nat` value is smaller than `n`
#guard_msgs (drop info) in
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type

end V1

namespace V2

index Client.Uid where
  UidMap => ClientMap
  UidMapD => ClientMapD

#guard_msgs (drop info) in
#check ClientMap
-- ClientMap (α : Type) : Type
#guard_msgs (drop info) in
#check ClientMapD
-- ClientMapD (len : Nat) (α : Type) : Type
#guard_msgs (drop info) in
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type

end V2

namespace V3

index Client.Uid where
  UidMap => Client.Map
  UidMapD => Client.MapD

#guard_msgs (drop info) in
#check Client.Map
-- Client.Map (α : Type) : Type
#guard_msgs (drop info) in
#check Client.MapD
-- Client.MapD (len : Nat) (α : Type) : Type
#guard_msgs (drop info) in
#check Client.Uid.FUid
-- Client.Uid.FUid (n : Nat) : Type

end V3

end Readme

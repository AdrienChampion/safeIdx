import SafeIdx



namespace SafeIdx.Tests.Client



/-- Client indices. -/
index Client.Idx where
  UidMap => Clients
  UidMapD => ClientsD

export Client.Idx (FUid)

structure Client where
  name : String
  email : String
  idx : Client.Idx
deriving Inhabited, Repr

instance : ToString Client where
  toString self :=
    s!"{self.name} <{self.email}> {self.idx}"

def Client.mk'
  (name email : String)
  (idx : Client.Idx.FUid n)
: Client :=
  ⟨name, email, idx⟩



def run : IO Unit := do
  println! "building `DMap`, accessing with indices from `DMap.pushIdx`"
  --  vvvvvvv~~~~ `Client.Idx.DArray 0 Client`
  let clients := ClientsD.mkEmpty 17
  --        vvvvvvv~~~~ `Client.Idx.DArray 1 Client`
  let (cat, clients) :=
    Client.mk' "cat" "cat@neko.nya"
    |> clients.pushIdx
  --        vvvvvvv~~~~ `Client.Idx.DArray 2 Client`
  let (dog, clients) :=
    Client.mk' "dog" "dog@inu.wan"
    |> clients.pushIdx
  --        vvvvvvv~~~~ `Client.Idx.DArray 3 Client`
  let (jef, clients) :=
    Client.mk' "jef" "jef@ningen.com"
    |> clients.pushIdx

  -- `GetElem` notation (`array[idx]`) requires a proof that the index is in-bound, which here is
  -- inferred automatically thanks to various lemmas behind the scene
  println! "  jef : {clients[jef]}"
  println! "  cat : {clients[cat]}"
  println! "  dog : {clients[dog]}"

  println! "\nfor-loop on `clients`"
  for client in clients do
    println! "- {client}"
  println! "\nfor-loop on `clients.iterIdx`"
  for (idx, client) in clients.iterIdx do
    println! "- {idx} ↦ {client}"
  println! "\nfor-loop on `clients.indices`"
  for idx in clients.indices do
    println! "- idx : {idx}"


  println! "\nfolding"
  let s := clients.foldlIdx
    (fun s uid client =>
      let sep := if s.isEmpty then "" else ", "
      s ++ sep ++ s!"{client} ({uid})")
    ""
  println! "- foldl : {s}"
  let s := clients.foldrIdx
    (fun uid client s =>
      let sep := if s.isEmpty then "" else ", "
      s ++ sep ++ s!"{client} ({uid})")
    ""
  println! "- foldr : {s}"


  println! "\n\nswitching to `Map`, accessing with indices from `DMap`:"
  --  vvvvvvvv~~~~ `Client.Idx.Array Client`, length has been erased from the type
  let clients' :=
    clients.toMap

  -- proof that indices are in-bound also inferred thanks to various lemmas again
  println! "  jef : {clients'[jef]}"
  println! "  cat : {clients'[cat]}"
  println! "  dog : {clients'[dog]}"


  println! "\nfolding"
  let s := clients'.foldlIdx
    (fun s uid client =>
      let sep := if s.isEmpty then "" else ", "
      s ++ sep ++ s!"{client} ({uid})")
    ""
  println! "- foldl : {s}"
  let s := clients'.foldrIdx
    (fun uid client s =>
      let sep := if s.isEmpty then "" else ", "
      s ++ sep ++ s!"{client} ({uid})")
    ""
  println! "- foldr : {s}"


  println! "\nfor-loop on `clients'`"
  for client in clients' do
    println! "- {client}"
  println! "\nfor-loop on `clients'.iterIdx`"
  for (idx, client) in clients'.iterIdx do
    println! "- {idx} ↦ {client}"
  println! "\nfor-loop on `clients'.indices`"
  for idx in clients'.indices do
    println! "- idx : {idx}"

/-- info:
building `DMap`, accessing with indices from `DMap.pushIdx`
  jef : jef <jef@ningen.com> #2
  cat : cat <cat@neko.nya> #0
  dog : dog <dog@inu.wan> #1

for-loop on `clients`
- cat <cat@neko.nya> #0
- dog <dog@inu.wan> #1
- jef <jef@ningen.com> #2

for-loop on `clients.iterIdx`
- #0<3 ↦ cat <cat@neko.nya> #0
- #1<3 ↦ dog <dog@inu.wan> #1
- #2<3 ↦ jef <jef@ningen.com> #2

for-loop on `clients.indices`
- idx : #0<3
- idx : #1<3
- idx : #2<3

folding
- foldl : cat <cat@neko.nya> #0 (#0<3), dog <dog@inu.wan> #1 (#1<3), jef <jef@ningen.com> #2 (#2<3)
- foldr : jef <jef@ningen.com> #2 (#2<3), dog <dog@inu.wan> #1 (#1<3), cat <cat@neko.nya> #0 (#0<3)


switching to `Map`, accessing with indices from `DMap`:
  jef : jef <jef@ningen.com> #2
  cat : cat <cat@neko.nya> #0
  dog : dog <dog@inu.wan> #1

folding
- foldl : cat <cat@neko.nya> #0 (#0<3), dog <dog@inu.wan> #1 (#1<3), jef <jef@ningen.com> #2 (#2<3)
- foldr : jef <jef@ningen.com> #2 (#2<3), dog <dog@inu.wan> #1 (#1<3), cat <cat@neko.nya> #0 (#0<3)

for-loop on `clients'`
- cat <cat@neko.nya> #0
- dog <dog@inu.wan> #1
- jef <jef@ningen.com> #2

for-loop on `clients'.iterIdx`
- #0<3 ↦ cat <cat@neko.nya> #0
- #1<3 ↦ dog <dog@inu.wan> #1
- #2<3 ↦ jef <jef@ningen.com> #2

for-loop on `clients'.indices`
- idx : #0<3
- idx : #1<3
- idx : #2<3
-/
#guard_msgs in
#eval run

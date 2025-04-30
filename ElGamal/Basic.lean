import Lean
import Std.Data.HashMap


def randInRange (lo hi : Nat) : IO Nat := do
  let g ← IO.rand lo hi
  pure g


-- representa um grupo cíclico finito com operação multiplicativa

structure Group where
  elems    : List Nat         -- elementos do grupo
  op       : Nat → Nat → Nat  -- operação (multiplicação modular, por exemplo)
  identity : Nat
  pow      : Nat → Nat → Nat  -- potência no grupo
  order    : Nat

instance : Repr Group where
  reprPrec g _ := s!"Group({g.elems}, {g.identity}, {g.order})"


-- cria um grupo multiplicativo mod p

def modGroup (p : Nat) : Group :=
  { elems := List.range p |>.filter (· ≠ 0),
    op := fun a b => (a * b) % p,
    identity := 1,
    pow := fun a e => Nat.pow a e % p,
    order := p - 1 }

#eval modGroup 7

-- ElGamal chave pública
structure PublicKey where
  g : Nat
  h : Nat
deriving BEq, Repr

instance : ToString PublicKey where
  toString pk := s!"PublicKey(g: {pk.g}, h: {pk.h})"

-- ElGamal chave privada
structure SecretKey where
  x : Nat
deriving BEq, Repr


-- Ciphertext
structure Ciphertext where
  c1 : Nat
  c2 : Nat
  deriving BEq, Repr

instance : ToString Ciphertext where
  toString ct := s!"Ciphertext(c1: {ct.c1}, c2: {ct.c2})"


-- ElGamal Encrypt
def elgamalEncrypt (grp : Group) (pk : PublicKey) (m r : Nat) : Ciphertext :=
  { c1 := grp.pow pk.g r,
    c2 := (m * grp.pow pk.h r) % (grp.order + 1) }

def encryptMessage (grp : Group) (pk : PublicKey) (m : Nat) : IO Ciphertext := do
  let r ← IO.rand 1 grp.order
  pure (elgamalEncrypt grp pk m r)

-- Jogo IND-CPA - Game 0 (real encryption)
def game0 (grp : Group) (pk : PublicKey) (m0 m1 : Nat) (b r : Nat) : Ciphertext :=
  let mb := if b = 0 then m0 else m1
  elgamalEncrypt grp pk mb r

-- Jogo IND-CPA - Game 1 (usa R aleatório ao invés de h^r)
def game1 (grp : Group) (pk : PublicKey) (m0 m1 : Nat) (b r R : Nat) : Ciphertext :=
  let mb := if b = 0 then m0 else m1
  { c1 := grp.pow pk.g r,
    c2 := (mb * R) % (grp.order + 1) }

-- Jogo IND-CPA - Game 2 (mensagem fixa, m0)
def game2 (grp : Group) (pk : PublicKey) (m0 : Nat) (r R : Nat) : Ciphertext :=
  { c1 := grp.pow pk.g r,
    c2 := (m0 * R) % (grp.order + 1) }

/-
  * ERROR *
   inverse modular arithmetic -/

def invMod (a b : Nat) : Nat := b / a

def elgamalDecrypt (grp : Group) (sk : SecretKey) (ct : Ciphertext) : Nat :=
  let s := grp.pow ct.c1 sk.x
  let s_inv := invMod s (grp.order + 1)
  (ct.c2 * s_inv) % (grp.order + 1)

def generateKeyPair (grp : Group) : IO (PublicKey × SecretKey) := do
  let x ← IO.rand 1 grp.order
  let g := grp.elems.head! -- assume já validado como gerador
  let h := grp.pow g x
  pure ({ g := g, h := h }, { x := x })


def simulator : IO Unit := do
  let grp := modGroup 7
  let (pk, sk) ← generateKeyPair grp   -- Alice gera chave
  IO.println s!"Alice publica pk = {pk}"
  let m := 5
  IO.println s!"Bob quer enviar m = {m} para Alice"
  let ct ← encryptMessage grp pk m
  IO.println s!"Bob envia ciphertext = {ct}"
  let m' := elgamalDecrypt grp sk ct
  IO.println s!"Alice decifra e obtém m' = {m'}"

#eval simulator


-- Adversário: tenta adivinhar b a partir do ciphertext

abbrev Adversary := Ciphertext → Nat -- retorna 0 ou 1

abbrev AdversaryIO := Ciphertext → IO Nat


-- Indistinguibilidade experimental: diferença de sucesso do adversário
partial def runExp (n : Nat) (adv : AdversaryIO)
    (gameGen : Nat → IO Ciphertext) : IO Nat := do
  let mut win := 0
  for i in [0:n] do
    -- dbg_trace "run {i}"
    let ct ← gameGen i
    let guess ← adv ct
    if guess = 0 then
      win := win + 1
  pure win

-- Simular a vantagem do adversário entre dois jogos
partial def computeAdvantage
    (n : Nat)
    (adv : AdversaryIO)
    (game0 : Nat → IO Ciphertext)
    (game1 : Nat → IO Ciphertext) : IO Float := do
  let win0 ← runExp n adv game0
  let win1 ← runExp n adv game1
  dbg_trace s!"win0: {win0}, win1: {win1}"
  pure (Float.ofNat (win0 - win1) / Float.ofNat n)


-- Exemplo de grupo com p = 7

def exampleGroup := modGroup 7

def examplePk : PublicKey := { g := 3, h := 5 }

def exampleAdversary : Adversary := fun ct =>
  if ct.c2 % 2 == 0 then 0 else 1

def exampleAdversaryIO : AdversaryIO :=
  fun ct => pure (if ct.c2 % 2 == 0 then 0 else 1)

-- Simuladores para b = 0 e b = 1 usando valores fixos (aleatoriedade simulada)
def fixedGame0 (b : Nat) : Nat → Ciphertext :=
  fun i => game0 exampleGroup examplePk 2 4 b ((i+3) % 6 + 1)

def fixedGame1 (b : Nat) : Nat → Ciphertext :=
  fun i => game1 exampleGroup examplePk 2 4 b ((i+3) % 6 + 1) ((i+5) % 6 + 1)


-- Simuladores para b = 0 e b = 1 usando valores aleatoriedade simulados

def randomGame0 (grp : Group) (pk : PublicKey) (m0 m1 : Nat) (b : Nat)
  : IO Ciphertext := do
  let r ← IO.rand 1 grp.order
  pure (game0 grp pk m0 m1 b r)

def randomGame1 (grp : Group) (pk : PublicKey) (m0 m1 : Nat) (b : Nat)
  : IO Ciphertext := do
  let r ← IO.rand 1 grp.order
  let R ← IO.rand 1 grp.order
  pure (game1 grp pk m0 m1 b r R)


-- Rodar comparação de vantagem
#eval computeAdvantage 4000 exampleAdversaryIO
  (randomGame0 exampleGroup examplePk 2 4)
  (randomGame1 exampleGroup examplePk 2 4)

-- Type-checker for the simply-typed lambda calculus
--
-- Where we factorize canonical and elimination forms in terms

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_) renaming (true to True ; false to False)
open import Data.Maybe
open import Data.Maybe.Categorical renaming (monad to monadMaybe)
open import Data.List hiding ([_])
open import Data.Nat hiding (_*_ ; _+_ ; _≟_)
open import Data.Product

open import Level
open import Function hiding (_∋_)

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Monad
open RawMonad {{...}}

instance MonadMaybe = monadMaybe

infix 5 _⊢?_∋_
infix 5 _⊢?_∈
infix 20 _∈?_
infixr 30 _+_
infixr 35 _*_
infixr 40 _⇒_
infixl 150 _▹_

-- * Types

data type : Set where
  unit nat : type
  _*_ _+_ _⇒_ : (A B : type) → type

bool : type
bool = unit + unit


_≟_ : type → type → Bool
unit      ≟ unit       = True
nat       ≟ nat        = True
(A₁ + B₁) ≟ (A₂ + B₂)  = A₁ ≟ A₂ ∧ B₁ ≟ B₂
(A₁ ⇒ B₁) ≟ (A₂ ⇒ B₂)  = A₁ ≟ A₂ ∧ B₁ ≟ B₂
(A₁ * B₁) ≟ (A₂ * B₂)  = A₁ ≟ A₂ ∧ B₁ ≟ B₂
_         ≟ _          = False

-- * Syntax of terms

data dir : Set where
  ⇑ ⇓ : dir

data can (T : Set) : Set where
  tt        :               can T
  pair      : (t₁ t₂ : T) → can T
  lam       : (b : T)     → can T
  ze        :               can T
  su        : (t : T)     → can T
  inj₁ inj₂ : (t : T)     → can T

data elim (T : Set) : dir → Set where
  apply   : (s : T)     → elim T ⇑
  fst snd :               elim T ⇑
  split   : (c₁ c₂ : T) → elim T ⇓

data term : dir → Set  where
  C       : (c : can (term ⇓))                           → term ⇓
  inv     : (t : term ⇑)                                 → term ⇓
  var     : (k : ℕ)                                      → term ⇑
  _#_     : ∀ {d} → (n : term ⇑)(args : elim (term ⇓) d) → term d
  [_:∋:_] : (T : type)(t : term ⇓)                       → term ⇑

pattern Ctt       = C tt
pattern Cze       = C ze
pattern Csu x     = C (su x)
pattern Cpair x y = C (pair x y)
pattern Clam b    = C (lam b)
pattern Cinj₁ x   = C (inj₁ x)
pattern Cinj₂ x   = C (inj₂ x)

-- ** Tests

true : term ⇓
true = Cinj₁ Ctt

false : term ⇓
false = Cinj₂ Ctt

t1 : term ⇓
t1 = inv ([ nat ⇒ nat :∋: Clam {- x -} (inv (var {- x -} 0)) ] # apply (Csu (Csu Cze)))

t2 : term ⇓
t2 = Clam {-x-} (var {- x -} 0 # split true false)

-- * Type-checking

context = List type

pattern _▹_ Γ T = T ∷ Γ
pattern ε       = []

_∈?_ : ℕ → context → Maybe type
_     ∈? ε      = nothing
zero  ∈? Γ ▹ T  = return T
suc n ∈? Γ ▹ T  = n ∈? Γ

_=?=_ : type → type → Maybe ⊤
A =?= B = if A ≟ B then return tt else nothing

-- XXX: Mutually-recursive to please the termination checker
_⊢?_∋_     : context → type → term ⇓ → Maybe ⊤
_⊢?_∈      : context → term ⇑ → Maybe type
_⊢?_∋C_    : context → type → can (term ⇓) → Maybe ⊤
_!_⊢?_∋#_  : context → type → type → elim (term ⇓) ⇓ → Maybe ⊤
_!_⊢?_∈#   : context → type → elim (term ⇓) ⇑ → Maybe type

Γ ⊢? unit ∋ Ctt = return tt
Γ ⊢? T ∋ C t = Γ ⊢? T ∋C t
Γ ⊢? T ∋ inv t =
  do T' ← (Γ ⊢? t ∈)
     T =?= T'
Γ ⊢? A ∋ f # e =
  do T ← Γ ⊢? f ∈
     Γ ! T ⊢? A ∋# e

Γ ⊢? var k ∈ = k ∈? Γ
Γ ⊢? f # e ∈ =
  do T ← Γ ⊢? f ∈
     Γ ! T ⊢? e ∈#
Γ ⊢? [ T :∋: t ] ∈ =
  do _ ← Γ ⊢? T ∋ t
     return T

Γ ⊢? A * B ∋C pair t₁ t₂ =
  do _ ← Γ ⊢? A ∋ t₁
     _ ← Γ ⊢? B ∋ t₂
     return tt
Γ ⊢? A ⇒ B ∋C lam b =
  do _ ← Γ ▹ A ⊢? B ∋ b
     return tt
Γ ⊢? nat ∋C ze =
  return tt
Γ ⊢? nat ∋C su n =
  do _ ← Γ ⊢? nat ∋ n
     return tt
Γ ⊢? A + B ∋C inj₁ t =
  do _ ← Γ ⊢? A ∋ t
     return tt
Γ ⊢? A + B ∋C inj₂ t =
  do _ ← Γ ⊢? B ∋ t
     return tt
Γ ⊢? T ∋C t = nothing

Γ ! A ⇒ B ⊢? apply s ∈# =
  do _ ← Γ ⊢? A ∋ s
     return B
Γ ! A * B ⊢? fst ∈# =
  return A
Γ ! A * B ⊢? snd ∈# =
  return B
_ ! _ ⊢? _ ∈# = nothing
Γ ! nat ⊢? A ∋# split c₁ c₂ =
  do _ ← Γ ▹ A ⊢? A ∋ c₁
     _ ← Γ ⊢? A ∋ c₂
     return tt
Γ ! X + Y ⊢? A ∋# split c₁ c₂ =
  do _ ← Γ ▹ X ⊢? A ∋ c₁
     _ ← Γ ▹ Y ⊢? A ∋ c₂
     return tt
Γ ! _ ⊢? _ ∋# _ = nothing

-- ** Tests

nat∋t1 : [] ⊢? nat ∋ t1 ≡ just tt
nat∋t1 = refl

T1 : type
T1 = nat ⇒ (unit + unit)

T2 : type
T2 = (nat + unit) ⇒ (unit + unit)

T1∋t2 : [] ⊢? T1 ∋ t2 ≡ just tt
T1∋t2 = refl

T2∋t2 : [] ⊢? T2 ∋ t2 ≡ just tt
T2∋t2 = refl

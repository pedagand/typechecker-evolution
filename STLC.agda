-- Type-checker for the simply-typed lambda calculus
--
-- Where we use a few inductive families to implement the bidirectional
-- syntax but we nonetheless fail to avoid a mutually-recursive
-- definition of the type-checker because the termination checker is
-- confused by the packing/unpacking of the `In` constructors.

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.Bool hiding (_≟_) renaming (true to True ; false to False)
open import Data.Maybe
open import Data.List hiding ([_])
open import Data.Nat hiding (_*_ ; _+_ ; _≟_)
open import Data.Product

open import Level
open import Function hiding (_∋_)

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import Category.Monad
-- <XXX>
-- This should have been defined in Category.Monad. It Will be
-- made irrelevant by native support of do-notation in Agda 2.6 see
-- https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html
infix -10 do_
do_ : ∀ {a} {A : Set a} → A → A
do x = x
infixr 0 do-bind
syntax do-bind  m (λ x → m₁) = x ← m -| m₁
open RawMonadZero {Level.zero} Data.Maybe.monadZero
do-bind = _>>=_
-- </XXX>


infix 5 _⊢?_
infix 5 _⊢C?_∋_
infix 5 _!_⊢E?_
infix 10 _∈
infix 10 _∋_
infix 20 _∈?_
infix 25 _▹_
infixr 30 _+_
infixr 35 _*_
infixr 40 _⇒_


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
_     ∈? ε      = ∅
zero  ∈? Γ ▹ T  = return T
suc n ∈? Γ ▹ T  = n ∈? Γ

_=?=_ : type → type → Maybe ⊤
A =?= B = if A ≟ B then return tt else ∅

data In (P : dir → Set) : dir → Set where
  _∋_ : (T : type)(t : P ⇓) → In P ⇓
  _∈ : (t : P ⇑) → In P ⇑

Out : dir → Set
Out ⇑ = type
Out ⇓ = ⊤

{-# TERMINATING #-}
_⊢?_     : ∀ {d} → context → In term d → Maybe (Out d)
_⊢C?_∋_  : context → type → can (term ⇓) → Maybe ⊤
_!_⊢E?_  : ∀ {d} → context → type → In (elim (term ⇓)) d → Maybe (Out d)


Γ ⊢? unit ∋ Ctt = return tt
Γ ⊢? T ∋ C t = Γ ⊢C? T ∋ t
Γ ⊢? T ∋ inv t =
  do T' ← (Γ ⊢? t ∈)
  -| T =?= T'
Γ ⊢? A ∋ f # e =
  -- XXX: how to factorize with `Γ ⊢? f # e ∈`?
  do T ← Γ ⊢? f ∈
  -| Γ ! T ⊢E? A ∋ e

Γ ⊢? var k ∈ = k ∈? Γ
Γ ⊢? f # e ∈ = 
  do T ← Γ ⊢? f ∈
  -| Γ ! T ⊢E? e ∈
Γ ⊢? [ T :∋: t ] ∈ =
  do _ ← Γ ⊢? T ∋ t
  -| return T

Γ ⊢C? A * B ∋ pair t₁ t₂ =
  do _ ← Γ ⊢? A ∋ t₁
  -| _ ← Γ ⊢? B ∋ t₂
  -| return tt
Γ ⊢C? A ⇒ B ∋ lam b =
  do _ ← Γ ▹ A ⊢? B ∋ b
  -| return tt
Γ ⊢C? nat ∋ ze =
  return tt
Γ ⊢C? nat ∋ su n =
  do _ ← Γ ⊢? nat ∋ n
  -| return tt
Γ ⊢C? A + B ∋ inj₁ t =
  do _ ← Γ ⊢? A ∋ t
  -| return tt
Γ ⊢C? A + B ∋ inj₂ t =
  do _ ← Γ ⊢? B ∋ t
  -| return tt
Γ ⊢C? T ∋ t = ∅

Γ ! A ⇒ B ⊢E? apply s ∈ =
  do _ ← Γ ⊢? A ∋ s
  -| return B
Γ ! A * B ⊢E? fst ∈ =
  return A
Γ ! A * B ⊢E? snd ∈ =
  return B
_ ! _ ⊢E? _ ∈ = ∅
Γ ! nat ⊢E? A ∋ split c₁ c₂ =
  do _ ← Γ ▹ A ⊢? A ∋ c₁
  -| _ ← Γ ⊢? A ∋ c₂
  -| return tt
Γ ! X + Y ⊢E? A ∋ split c₁ c₂ =
  do _ ← Γ ▹ X ⊢? A ∋ c₁
  -| _ ← Γ ▹ Y ⊢? A ∋ c₂
  -| return tt
Γ ! _ ⊢E? _ ∋ _ = ∅


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

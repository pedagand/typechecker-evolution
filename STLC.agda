-- Type-checker for the simply-typed lambda calculus
--
-- Where we use an inductive family to implement the bidirectional
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
infix 10 _∈
infix 10 _∋_
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

data term : dir → Set  where
  tt            :                                term ⇓
  pair          : (t₁ t₂ : term ⇓)             → term ⇓
  lam           : (b : term ⇓)                 → term ⇓
  ze            :                                term ⇓
  su            : (t : term ⇓)                 → term ⇓
  inj₁ inj₂     : (t : term ⇓)                 → term ⇓
  inv           : (t : term ⇑)                 → term ⇓
  var           : (k : ℕ)                      → term ⇑
  _#apply_      : (n : term ⇑)(s : term ⇓)     → term ⇑
  _#fst _#snd   : (n : term ⇑)                 → term ⇑
  _#split[_/_]  : (n : term ⇑)(c₁ c₂ : term ⇓) → term ⇓
  [_:∋:_]       : (T : type)(t : term ⇓)       → term ⇑

-- ** Tests

true : term ⇓
true = inj₁ tt

false : term ⇓
false = inj₂ tt

t1 : term ⇓
t1 = inv ([ nat ⇒ nat :∋: lam {- x -} (inv (var {- x -} 0)) ] #apply (su (su ze)))

t2 : term ⇓
t2 = lam {-x-} (var {- x -} 0 #split[ true / false ])

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

data In : dir → Set where
  _∋_ : (T : type)(t : term ⇓) → In ⇓
  _∈ : (t : term ⇑) → In ⇑

Out : dir → Set
Out ⇑ = type
Out ⇓ = ⊤

{-# TERMINATING #-}
_⊢?_ : ∀ {d} → context → In d → Maybe (Out d)
Γ ⊢? unit ∋ tt = return tt
Γ ⊢? A * B ∋ pair t₁ t₂ =
  do _ ← Γ ⊢? A ∋ t₁
  -| _ ← Γ ⊢? B ∋ t₂
  -| return tt
Γ ⊢? A ⇒ B ∋ lam b =
  do _ ← Γ ▹ A ⊢? B ∋ b
  -| return tt
Γ ⊢? nat ∋ ze =
  return tt
Γ ⊢? nat ∋ su n =
  do _ ← Γ ⊢? nat ∋ n
  -| return tt
Γ ⊢? A + B ∋ inj₁ t =
  do _ ← Γ ⊢? A ∋ t
  -| return tt
Γ ⊢? A + B ∋ inj₂ t =
  do _ ← Γ ⊢? B ∋ t
  -| return tt
Γ ⊢? T ∋ inv t =
  do T' ← (Γ ⊢? t ∈)
  -| T =?= T'
Γ ⊢? A ∋ t #split[ t₁ / t₂ ] =
    do T ← Γ ⊢? t ∈
    -| return tt
Γ ⊢? _ ∋ _ = ∅


Γ ⊢? var k ∈ = k ∈? Γ
Γ ⊢? f #apply s ∈ =
  do T ← Γ ⊢? f ∈
  -| case T of λ {
     (A ⇒ B) →
       do _ ← Γ ⊢? A ∋ s
       -| return B ;
     _       → ∅ }
Γ ⊢? p #fst ∈ =
  do T ← Γ ⊢? p ∈
  -| case T of λ {
     (A * B) → return A ;
     _       → ∅ }
Γ ⊢? p #snd ∈ =
  do T ← Γ ⊢? p ∈
  -| case T of λ {
     (A * B) → return B ;
     _       → ∅ }
Γ ⊢? [ T :∋: t ] ∈ =
  do _ ← Γ ⊢? T ∋ t
  -| return T

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

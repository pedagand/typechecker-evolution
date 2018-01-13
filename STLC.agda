-- Type-checker for the simply-typed lambda calculus
--
-- Where we use an inductive family to implement the bidirectional syntax.

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
_     ∈? ε      = nothing
zero  ∈? Γ ▹ T  = return T
suc n ∈? Γ ▹ T  = n ∈? Γ

_=?=_ : type → type → Maybe ⊤
A =?= B = if A ≟ B then return tt else nothing

-- XXX: Mutually-recursive to please the termination checker
_⊢?_∋_ : context → type → term ⇓ → Maybe ⊤
_⊢?_∈  : context → term ⇑ → Maybe type

Γ ⊢? unit ∋ tt = return tt
Γ ⊢? A * B ∋ pair t₁ t₂ =
  do _ ← Γ ⊢? A ∋ t₁
     _ ← Γ ⊢? B ∋ t₂
     return tt
Γ ⊢? A ⇒ B ∋ lam b =
  do _ ← Γ ▹ A ⊢? B ∋ b
     return tt
Γ ⊢? nat ∋ ze =
  return tt
Γ ⊢? nat ∋ su n =
  do _ ← Γ ⊢? nat ∋ n
     return tt
Γ ⊢? A + B ∋ inj₁ t =
  do _ ← Γ ⊢? A ∋ t
     return tt
Γ ⊢? A + B ∋ inj₂ t =
  do _ ← Γ ⊢? B ∋ t
     return tt
Γ ⊢? T ∋ inv t =
  do T' ← (Γ ⊢? t ∈)
     T =?= T'
Γ ⊢? A ∋ t #split[ t₁ / t₂ ] =
    do T ← Γ ⊢? t ∈
       return tt
Γ ⊢? _ ∋ _ = nothing


Γ ⊢? var k ∈ = k ∈? Γ
Γ ⊢? f #apply s ∈ =
  do A ⇒ B ← Γ ⊢? f ∈
       where _ → nothing
     _ ← Γ ⊢? A ∋ s
     return B
Γ ⊢? p #fst ∈ =
  do A * B ← Γ ⊢? p ∈
       where _ → nothing
     return A
Γ ⊢? p #snd ∈ =
  do A * B ← Γ ⊢? p ∈
       where _ → nothing
     return B
Γ ⊢? [ T :∋: t ] ∈ =
  do _ ← Γ ⊢? T ∋ t
     return T

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

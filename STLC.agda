-- Type-checker for the simply-typed lambda calculus
--
-- Where the typechecker is defined for any monad offering an
-- un-catchable failure operation.

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

data term : Set where
  tt              :                                      term
  pair            : (t₁ t₂ : term)                     → term
  lam`_`          : (A : type)(b : term)               → term
  ze              :                                      term
  su              : (t : term)                         → term
  inj₁`_`         : (B : type)(t : term)               → term
  inj₂`_`         : (A : type)(t : term)               → term
  _#split`_`[_/_] : (n : term)(A : type)(c₁ c₂ : term) → term
  var             : (k : ℕ)                            → term
  _#apply_        : (n : term)(s : term)               → term
  _#fst _#snd     : (n : term)                         → term

-- ** Tests

true : term
true = inj₁` unit ` tt

false : term
false = inj₂` unit ` tt

t1 : term
t1 = (lam` nat ` {- x -} (var {- x -} 0)) #apply (su (su ze))


t2 : term
t2 = lam` nat ` {-x-} (var {- x -} 0 #split` bool `[ true / false ])

t2' : term
t2' = lam` nat + unit ` {-x-} (var {- x -} 0 #split` bool `[ true / false ])

-- * Type-checking

context = List type

pattern _▹_ Γ T = T ∷ Γ
pattern ε       = []

module TC (M : Set → Set)(ops : RawMonadZero M) where

  infix 5 _⊢?_∈
  infix 20 _∈?_

  open RawMonadZero ops

  -- <XXX> 
  -- This should have been defined in Category.Monad. It will be
  -- made irrelevant by native support of do-notation in Agda 2.6 see
  -- https://agda.readthedocs.io/en/latest/language/syntactic-sugar.html
  infix -10 do_
  do_ : ∀ {a} {A : Set a} → A → A
  do x = x
  infixr 0 do-bind
  syntax do-bind  m (λ x → m₁) = x ← m -| m₁
  do-bind = _>>=_
  -- </XXX>


  _∈?_ : ℕ → context → M type
  _     ∈? ε      = ∅
  zero  ∈? Γ ▹ T  = return T
  suc n ∈? Γ ▹ T  = n ∈? Γ


  _=?=_ : type → type → M ⊤
  A =?= B = if A ≟ B then return tt else ∅


  _⊢?_∈  : context → term → M type
  Γ ⊢? tt ∈ = return unit
  Γ ⊢? pair t₁ t₂ ∈ = 
    do A ← Γ ⊢? t₁ ∈
    -| B ← Γ ⊢? t₂ ∈
    -| return (A * B)
  Γ ⊢? lam` A ` b ∈ = 
    do B ← Γ ▹ A ⊢? b ∈
    -| return (A ⇒ B)
  Γ ⊢? ze ∈ = 
    return nat
  Γ ⊢? su n ∈ = 
    do T ← Γ ⊢? n ∈
    -| _ ← (T =?= nat)
    -| return nat
  Γ ⊢? inj₁` B ` t ∈ = 
       do A ← Γ ⊢? t ∈
    -| return (A + B)
  Γ ⊢? inj₂` A ` t ∈ = 
    do B ← Γ ⊢? t ∈
    -| return (A + B)
  Γ ⊢? t #split` A `[ t₁ / t₂ ] ∈ = 
    do T ← Γ ⊢? t ∈
    -| case T of λ {
       nat → 
         do T₁ ← Γ ▹ A ⊢? t₁ ∈
         -| T₂ ← Γ ⊢? t₂ ∈
         -| _ ← T₂ =?= A
         -| return A ;
       (X + Y) → 
         do T₁ ← Γ ▹ X ⊢? t₁ ∈
         -| T₂ ← Γ ▹ Y ⊢? t₂ ∈
         -| _ ← T₁ =?= A
         -| return A ;
       _ → ∅ }

  Γ ⊢? var k ∈ = k ∈? Γ
  Γ ⊢? f #apply s ∈ =
    do T ← Γ ⊢? f ∈
    -| case T of λ {
      (A ⇒ B) → 
         do T ← Γ ⊢? s ∈
         -| _ ← A =?= T
         -| return B ;
      _      → ∅ }
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

-- ** Tests

open TC Maybe Data.Maybe.monadZero

nat∋t1 : [] ⊢? t1 ∈ ≡ just nat
nat∋t1 = refl

T1∋t2 : [] ⊢? t2 ∈ ≡ just (nat ⇒ (unit + unit))
T1∋t2 = refl

T2∋t2 : [] ⊢? t2' ∈ ≡ just ((nat + unit) ⇒ (unit + unit))
T2∋t2 = refl

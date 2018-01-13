-- Type-checker for the simply-typed lambda calculus
--
-- Where we write Haskell98 on a fully annotated syntax.

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

_∈?_ : ℕ → context → Maybe type
_     ∈? ε      = nothing
zero  ∈? Γ ▹ T  = return T
suc n ∈? Γ ▹ T  = n ∈? Γ

_=?=_ : type → type → Maybe ⊤
A =?= B = if A ≟ B then return tt else nothing

_⊢?_∈  : context → term → Maybe type
Γ ⊢? tt ∈ = return unit
Γ ⊢? pair t₁ t₂ ∈ = 
  do A ← Γ ⊢? t₁ ∈
     B ← Γ ⊢? t₂ ∈
     return (A * B)
Γ ⊢? lam` A ` b ∈ = 
  do B ← Γ ▹ A ⊢? b ∈
     return (A ⇒ B)
Γ ⊢? ze ∈ = 
  return nat
Γ ⊢? su n ∈ = 
  do T ← Γ ⊢? n ∈
     _ ← (T =?= nat)
     return nat
Γ ⊢? inj₁` B ` t ∈ = 
  do A ← Γ ⊢? t ∈
     return (A + B)
Γ ⊢? inj₂` A ` t ∈ = 
  do B ← Γ ⊢? t ∈
     return (A + B)
Γ ⊢? t #split` A `[ t₁ / t₂ ] ∈ = 
    do nat ← Γ ⊢? t ∈
         where X + Y → do T₁ ← Γ ▹ X ⊢? t₁ ∈
                          T₂ ← Γ ▹ Y ⊢? t₂ ∈
                          _ ← T₁ =?= A
                          return A
               _ → nothing
       T₁ ← Γ ▹ A ⊢? t₁ ∈
       T₂ ← Γ ⊢? t₂ ∈
       _ ← T₂ =?= A
       return A
Γ ⊢? var k ∈ = k ∈? Γ
Γ ⊢? f #apply s ∈ =
  do A ⇒ B ← Γ ⊢? f ∈
       where _ → nothing
     T ← Γ ⊢? s ∈
     _ ← A =?= T
     return B
Γ ⊢? p #fst ∈ = 
  do A * B ← Γ ⊢? p ∈ 
       where _ → nothing
     return A
Γ ⊢? p #snd ∈ =
  do A * B ← Γ ⊢? p ∈
       where _ → nothing
     return B

-- ** Tests

nat∋t1 : [] ⊢? t1 ∈ ≡ just nat
nat∋t1 = refl

T1∋t2 : [] ⊢? t2 ∈ ≡ just (nat ⇒ (unit + unit))
T1∋t2 = refl

T2∋t2 : [] ⊢? t2' ∈ ≡ just ((nat + unit) ⇒ (unit + unit))
T2∋t2 = refl

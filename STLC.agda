-- Type-checker for the simply-typed lambda calculus
--
-- Where we use a type family to encode the type system and the
-- typechecker produces such typing witnesses

open import Data.Empty
open import Data.Unit hiding (_≟_)
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
infix 50 _∈_
infix 50 _∈
infix 50 _∋_
infixl 150 _▹_

-- * Types

data type : Set where
  unit nat : type
  _*_ _+_ _⇒_ : (A B : type) → type

bool : type
bool = unit + unit


-- TODO: automate this definition using reflection of Agda in Agda
-- see https://github.com/UlfNorell/agda-prelude/blob/master/src/Tactic/Deriving/Eq.agda
_≟_ : Decidable {A = type} _≡_
unit      ≟ unit          = yes refl
nat       ≟ nat           = yes refl
(A₁ + B₁) ≟ (A₂ + B₂)
  with A₁ ≟ A₂ | B₁ ≟ B₂
... | yes refl | yes refl = yes refl
... | yes refl | no ¬p    = no (λ { refl → ¬p refl })
... | no ¬p | _           = no (λ { refl → ¬p refl })
(A₁ ⇒ B₁) ≟ (A₂ ⇒ B₂)
  with A₁ ≟ A₂ | B₁ ≟ B₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬p    = no λ { refl → ¬p refl }
... | no ¬p    | _        = no λ { refl → ¬p refl }
(A₁ * B₁) ≟ (A₂ * B₂)
  with A₁ ≟ A₂ | B₁ ≟ B₂
... | yes refl | yes refl = yes refl
... | yes _    | no ¬p    = no λ { refl → ¬p refl }
... | no ¬p    | q₂       = no λ { refl → ¬p refl }
unit      ≟ (_ ⇒ _)       = no λ {()}
unit      ≟ (_ * _)       = no λ {()}
unit      ≟ nat           = no λ {()}
unit      ≟ (_ + _)       = no λ {()}
nat       ≟ (_ ⇒ _)       = no λ {()}
nat       ≟ (_ * _)       = no λ {()}
nat       ≟ unit          = no λ {()}
nat       ≟ (_ + _)       = no λ {()}
(_ + _)   ≟ (_ ⇒ _)       = no λ {()}
(_ + _)   ≟ (_ * _)       = no λ {()}
(_ + _)   ≟ nat           = no λ {()}
(_ + _)   ≟ unit          = no λ {()}
(_ ⇒ _)   ≟ unit          = no λ {()}
(_ ⇒ _)   ≟ nat           = no λ {()}
(_ ⇒ _)   ≟ (_ * _)       = no λ {()}
(_ ⇒ _)   ≟ (_ + _)       = no λ {()}
(_ * _)   ≟ unit          = no λ {()}
(_ * _)   ≟ nat           = no λ {()}
(_ * _)   ≟ (_ ⇒ _)       = no λ {()}
(_ * _)   ≟ (_ + _)       = no λ {()}


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

-- * Type system

context = List type

pattern _▹_ Γ T = T ∷ Γ
pattern ε       = []

data _∈_ (T : type) : context → Set where
  here : ∀ {Γ} →

      ---------
      T ∈ Γ ▹ T

  there : ∀ {Γ T'} →

      T ∈ Γ
    → ----------
      T ∈ Γ ▹ T'

mutual

  data _C⊢[_]_ : context → dir → type → Set where
    lam : ∀ {Γ A B} →

        Γ ▹ A ⊢[ ⇓ ] B
      → ---------------
        Γ C⊢[ ⇓ ] A ⇒ B

    tt : ∀ {Γ} →

        --------------
        Γ C⊢[ ⇓ ] unit

    ze : ∀ {Γ} →

        -------------
        Γ C⊢[ ⇓ ] nat

    su : ∀ {Γ} →

        Γ ⊢[ ⇓ ] nat
      → -------------
        Γ C⊢[ ⇓ ] nat

    inj₁ : ∀ {Γ A B} →

        Γ ⊢[ ⇓ ] A
      → ---------------
        Γ C⊢[ ⇓ ] A + B

    inj₂ : ∀ {Γ A B} →

        Γ ⊢[ ⇓ ] B
      → ---------------
        Γ C⊢[ ⇓ ] A + B

    pair : ∀ {Γ A B} →

        Γ ⊢[ ⇓ ] A →
        Γ ⊢[ ⇓ ] B
      → ---------------
        Γ C⊢[ ⇓ ] A * B

  data _E⊢[_]_↝_ : context → dir → type → type → Set where
    apply : ∀ {Γ A B} →

        Γ ⊢[ ⇓ ] A
      → -------------------
        Γ E⊢[ ⇑ ] A ⇒ B ↝ B

    fst : ∀ {Γ A B} →

        -------------------
        Γ E⊢[ ⇑ ] A * B ↝ A

    snd : ∀ {Γ A B} →

        -------------------
        Γ E⊢[ ⇑ ] A * B ↝ B

    iter : ∀ {Γ A} →

        Γ ▹ A ⊢[ ⇓ ] A →
        Γ ⊢[ ⇓ ] A
      → -----------------
        Γ E⊢[ ⇓ ] nat ↝ A

    case : ∀ {Γ A B C} →

        Γ ▹ A ⊢[ ⇓ ] C →
        Γ ▹ B ⊢[ ⇓ ] C
      → -------------------
        Γ E⊢[ ⇓ ] A + B ↝ C

  data _⊢[_]_ : context → dir → type → Set where

    C : ∀ {Γ d T} →

        Γ C⊢[ d ] T
      → -----------
        Γ ⊢[ d ] T

    inv : ∀ {Γ T} →

        Γ ⊢[ ⇑ ] T
      → ----------
        Γ ⊢[ ⇓ ] T

    var : ∀ {Γ T} →

        T ∈ Γ
      → ----------
        Γ ⊢[ ⇑ ] T

    _#_ : ∀ {Γ d I O} →

        Γ ⊢[ ⇑ ] I →
        Γ E⊢[ d ] I ↝ O
      → ---------------
        Γ ⊢[ d ] O

    [_:∋:_by_] : ∀ {Γ A} →

        (B : type) → Γ ⊢[ ⇓ ] B → A ≡ B
      → -------------------------------
        Γ ⊢[ ⇑ ] A

-- ** Tests

⊢true : [] ⊢[ ⇓ ] bool
⊢true = C (inj₁ (C tt))

⊢false : [] ⊢[ ⇓ ] bool
⊢false = C (inj₂ (C tt))

⊢t1 : [] ⊢[ ⇓ ] nat
⊢t1 = inv ([ (nat ⇒ nat) :∋: (C (lam (inv (var here)))) by refl ]
          # (apply (C (su (C (su (C ze)))))))

-- * Type-checking

_∈?_ : ℕ → (Γ : context) → Maybe (Σ[ T ∈ type ] T ∈ Γ)
_     ∈? ε      = nothing
zero  ∈? Γ ▹ T  = return (T , here)
suc n ∈? Γ ▹ T  = do (T' , t) ← n ∈? Γ
                     return (T' , there t)

data Dir : dir → Set where
  _∈  : term ⇑        → Dir ⇑
  _∋_ : type → term ⇓ → Dir ⇓

_=?=_ : (A B : type) → Maybe (A ≡ B)
A =?= B with A ≟ B
... | yes p = return p
... | no _ = nothing

_⊢?_∋_ : (Γ : context)(T : type) → term ⇓ → Maybe (Γ ⊢[ ⇓ ] T)
_⊢?_∈  : (Γ : context) → term ⇑ → Maybe (Σ[ T ∈ type ] Γ ⊢[ ⇑ ] T)

_⊢?_∋C_ : (Γ : context)(T : type) → can (term ⇓) → Maybe (Γ C⊢[ ⇓ ] T)

_!_⊢?_∋#_  : (Γ : context) → (I : type)(O : type) → elim (term ⇓) ⇓ → Maybe (Γ E⊢[ ⇓ ] I ↝ O)
_!_⊢?_∈#   : (Γ : context) → (I : type) → elim (term ⇓) ⇑ → Maybe (Σ[ O ∈ type ] Γ E⊢[ ⇑ ] I ↝ O)

Γ ⊢? T ∋ C t = do Δ ← Γ ⊢? T ∋C t
                  return (C Δ)
Γ ⊢? T ∋ inv t =
  do (T' , Δ) ← (Γ ⊢? t ∈)
     refl ← (T =?= T')
     return (inv Δ)
Γ ⊢? A ∋ t # e =
  do (T , Δt) ← Γ ⊢? t ∈
     Δe ← Γ ! T ⊢? A ∋# e
     return (Δt # Δe)

Γ ⊢? var k ∈ =
  do (T , x) ← k ∈? Γ
     return (T , var x)
Γ ⊢? n # e ∈ =
  do (T , Δn) ← Γ ⊢? n ∈
     (O , Δe) ← Γ ! T ⊢? e ∈#
     return (O , Δn # Δe)
Γ ⊢? [ T :∋: t ] ∈ =
  do Δt ← Γ ⊢? T ∋ t
     return (-, [ T :∋: Δt by refl ])


Γ ⊢? unit ∋C tt = 
  return tt
Γ ⊢? A * B ∋C pair t₁ t₂ =
  do Δ₁ ← Γ ⊢? A ∋ t₁
     Δ₂ ← Γ ⊢? B ∋ t₂
     return (pair Δ₁ Δ₂)
Γ ⊢? A ⇒ B ∋C lam b =
  do Δ ← Γ ▹ A ⊢? B ∋ b
     return (lam Δ)
Γ ⊢? nat ∋C ze =
  return ze
Γ ⊢? nat ∋C su n =
  do Δ ← Γ ⊢? nat ∋ n
     return (su Δ)
Γ ⊢? A + B ∋C inj₁ t =
  do Δ ← Γ ⊢? A ∋ t
     return (inj₁ Δ)
Γ ⊢? A + B ∋C inj₂ t =
  do Δ ← Γ ⊢? B ∋ t
     return (inj₂ Δ)
Γ ⊢? _ ∋C _ = nothing


Γ ! nat ⊢? A ∋# split t₁ t₂ =
  do Δt₁ ← Γ ▹ A ⊢? A ∋ t₁
     Δt₂ ← Γ ⊢? A ∋ t₂
     return (iter Δt₁ Δt₂)
Γ ! X + Y ⊢? A ∋# split t₁ t₂ =
  do ΔcX ← Γ ▹ X ⊢? A ∋ t₁
     ΔcY ← Γ ▹ Y ⊢? A ∋ t₂
     return (case ΔcX ΔcY)
Γ ! unit ⊢? A ∋# t    = nothing
Γ ! T * T₁ ⊢? A ∋# t  = nothing
Γ ! T ⇒ T₁ ⊢? A ∋# t  = nothing

Γ ! A ⇒ B ⊢? apply s ∈#   =     
  do Δs ← Γ ⊢? A ∋ s
     return (_ , apply Δs)
Γ ! unit ⊢? apply s ∈#    = nothing
Γ ! nat ⊢? apply s ∈#     = nothing
Γ ! T * T₁ ⊢? apply s ∈#  = nothing
Γ ! T + T₁ ⊢? apply s ∈#  = nothing

Γ ! A * B ⊢? fst ∈#  = return (_ , snd)
Γ ! unit ⊢? fst ∈#   = nothing
Γ ! nat ⊢? fst ∈#    = nothing
Γ ! _ + _ ⊢? fst ∈#  = nothing
Γ ! _ ⇒ _ ⊢? fst ∈#  = nothing

Γ ! A * B ⊢? snd ∈#  = return (_ , fst)
Γ ! unit ⊢? snd ∈#   = nothing
Γ ! nat ⊢? snd ∈#    = nothing
Γ ! _ + _ ⊢? snd ∈#  = nothing
Γ ! _ ⇒ _ ⊢? snd ∈#  = nothing

-- ** Tests

nat∋t1 : [] ⊢[ ⇓ ] nat
nat∋t1 = to-witness-T ([] ⊢? nat ∋ t1) tt

T1 : type
T1 = nat ⇒ (unit + unit)

T2 : type
T2 = (nat + unit) ⇒ (unit + unit)

T1∋t2 : [] ⊢[ ⇓ ] T1
T1∋t2 = to-witness-T ([] ⊢? T1 ∋ t2) tt

T2∋t2 : [] ⊢[ ⇓ ] T2
T2∋t2 = to-witness-T ([] ⊢? T2 ∋ t2) tt


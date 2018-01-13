-- Type-checker for the simply-typed lambda calculus
--
-- Where we make sure that the typing derivations produced by the
-- typechecker correspond to the term fed to the typechecker.

open import Data.Empty
open import Data.Unit hiding (_≟_)
open import Data.List hiding ([_])
open import Data.Nat hiding (_*_ ; _+_ ; _≟_)
open import Data.Product

open import Relation.Nullary
open import Relation.Binary hiding (_⇒_)
open import Relation.Binary.PropositionalEquality hiding ([_])

infix 5 _⊢?_∋_
infix 5 _⊢?_∈
infix 19 _↪_
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

-- * Relating typing and terms

record _↪_ (S T : Set) : Set where
  field
    ⌊_⌋ : S → T

open _↪_ {{...}} public

instance
  VarRaw : ∀ {T Γ} → T ∈ Γ ↪ ℕ
  ⌊_⌋ {{ VarRaw }} here      = zero
  ⌊_⌋ {{ VarRaw }} (there x) = suc ⌊ x ⌋

  OTermRaw : ∀ {Γ T d} → Γ ⊢[ d ] T ↪ term d
  ⌊_⌋ {{OTermRaw}} (C (lam b))         = C (lam ⌊ b ⌋)
  ⌊_⌋ {{OTermRaw}} (C tt)              = C tt
  ⌊_⌋ {{OTermRaw}} (C ze)              = C ze
  ⌊_⌋ {{OTermRaw}} (C (su t))          = C (su ⌊ t ⌋)
  ⌊_⌋ {{OTermRaw}} (C (inj₁ t))        = C (inj₁ ⌊ t ⌋)
  ⌊_⌋ {{OTermRaw}} (C (inj₂ t))        = C (inj₂ ⌊ t ⌋)
  ⌊_⌋ {{OTermRaw}} (C (pair t₁ t₂))    = C (pair ⌊ t₁ ⌋ ⌊ t₂ ⌋)
  ⌊_⌋ {{OTermRaw}} (inv t)             = inv ⌊ t ⌋
  ⌊_⌋ {{OTermRaw}} (var x)             = var ⌊ x ⌋
  ⌊_⌋ {{OTermRaw}} (f # (apply s))     = ⌊ f ⌋ # apply ⌊ s ⌋
  ⌊_⌋ {{OTermRaw}} (p # fst)           = ⌊ p ⌋ # fst
  ⌊_⌋ {{OTermRaw}} (p # snd)           = ⌊ p ⌋ # snd
  ⌊_⌋ {{OTermRaw}} (t # case x y)      = ⌊ t ⌋ # split ⌊ x ⌋ ⌊ y ⌋
  ⌊_⌋ {{OTermRaw}} (t # iter fs fz)    = ⌊ t ⌋ # split ⌊ fs ⌋ ⌊ fz ⌋
  ⌊_⌋ {{OTermRaw}} [ T :∋: t by refl ] = [ T :∋: ⌊ t ⌋ ]

data _⊢_∋_ (Γ : context)(T : type){d} : term d → Set where
  well-typed : (Δ : Γ ⊢[ d ] T ) → Γ ⊢ T ∋ ⌊ Δ ⌋

-- TODO: one could prove that `Γ ⊢ T ∋ t` is H-prop when `t : term ⇓`, ie. we have
--     lemma-proof-irr : ∀ {Γ T}{t : term ⇓} → ∀ (pf₁ pf₂ : Γ ⊢ T ∋ t) → → pf₁ ≅ pf₂
-- but this requires proving that `⌊_⌋` is injective.

-- TODO: conversely, one should be able to prove that `Γ ⊢ T ∋ t` is
-- equivalent to `type` when `t : term ⇑` but I haven't tried.

-- ** Tests

bool∋true : [] ⊢ bool ∋ true
bool∋true = well-typed ⊢true

bool∋false : [] ⊢ bool ∋ false
bool∋false = well-typed ⊢false

nat∋t1 : [] ⊢ nat ∋ t1
nat∋t1 = well-typed ⊢t1

-- * Type-checking

-- ** View on variable lookup

data _∈-view_ : ℕ → context → Set where
  yes : ∀ {T Γ} → (x : T ∈ Γ)  → ⌊ x ⌋ ∈-view Γ
  no  : ∀ {Γ n} → n ∈-view Γ

_∈?_ : ∀ n Γ → n ∈-view Γ
_     ∈? ε      = no
zero  ∈? Γ ▹ T  = yes here
suc n ∈? Γ ▹ T
  with n ∈? Γ
... | yes t     = yes (there t)
... | no        = no

-- ** View on typing

data Dir : dir → Set where
  _∈  : term ⇑        → Dir ⇑
  _∋_ : type → term ⇓ → Dir ⇓

instance
  DirRaw : ∀ {Γ d T} → Γ ⊢[ d ] T ↪ Dir d
  ⌊_⌋ {{DirRaw {d = ⇑}}} e    = ⌊ e ⌋ ∈
  ⌊_⌋ {{DirRaw {d = ⇓}{T}}} e = T ∋ ⌊ e ⌋

data _⊢[_]-view_ (Γ : context)(d : dir) : Dir d → Set where
  yes : ∀ {T} (Δ : Γ ⊢[ d ] T)   → Γ ⊢[ d ]-view ⌊ Δ ⌋
  no  : ∀ {t}                    → Γ ⊢[ d ]-view t

isYes : ∀ {Γ T t} → Γ ⊢[ ⇓ ]-view T ∋ t → Set
isYes (yes Δ) = ⊤
isYes no      = ⊥

lemma : ∀ {Γ T t} → (pf : Γ ⊢[ ⇓ ]-view T ∋ t) → isYes pf → Γ ⊢ T ∋ t
lemma (yes Δ) tt = well-typed Δ
lemma no ()

-- XXX: Mutually-recursive to please the termination checker
_⊢?_∋_  : (Γ : context)(T : type)(t : term ⇓) → Γ ⊢[ ⇓ ]-view T ∋ t
_⊢?_∈   : (Γ : context)(t : term ⇑) → Γ ⊢[ ⇑ ]-view t ∈

_⊢?_∋C_ : (Γ : context)(T : type)(t : can (term ⇓)) → Γ ⊢[ ⇓ ]-view T ∋ C t

_!_∋_⊢?_∋#_  : (Γ : context)(I : type)(Δt : Γ ⊢[ ⇑ ] I)(T : type)(e : elim (term ⇓) ⇓) → Γ ⊢[ ⇓ ]-view T ∋ (⌊ Δt ⌋ # e)
_!_∋_⊢?_∈#   : (Γ : context)(T : type)(Δt : Γ ⊢[ ⇑ ] T)(e : elim (term ⇓) ⇑) → Γ ⊢[ ⇑ ]-view (⌊ Δt ⌋ # e) ∈


Γ ⊢? T ∋ C t      = Γ ⊢? T ∋C t
Γ ⊢? T ∋ inv t
  with Γ ⊢? t ∈
... | no          = no
... | yes {T'} Δ
    with T' ≟ T
... | yes refl    = yes (inv Δ)
... | no ¬p       = no
Γ ⊢? A ∋ t # e
  with Γ ⊢? t ∈
... | no          = no
... | yes {T} Δ   = Γ ! T ∋ Δ ⊢? A ∋# e


Γ ⊢? var k ∈
  with k ∈? Γ
... | yes x       = yes (var x)
... | no          = no
Γ ⊢? f # e ∈
  with Γ ⊢? f ∈
... | yes {T} Δ   = Γ ! T ∋ Δ ⊢? e ∈#
... | no          = no
Γ ⊢? [ T :∋: t ] ∈
  with Γ ⊢? T ∋ t
... | yes Δ       = yes [ T :∋: Δ by refl ]
... | no          = no


Γ ⊢? unit ∋C tt  = yes (C tt)
Γ ⊢? unit ∋C _   = no

Γ ⊢? A * B ∋C pair t₁ t₂
  with Γ ⊢? A ∋ t₁ | Γ ⊢? B ∋ t₂
... | yes Δ₁ | yes Δ₂  = no
... | yes Δ₁ | no      = no
... | no     | _       = no
Γ ⊢? A * B ∋C _        = no

Γ ⊢? A ⇒ B ∋C lam b
  with Γ ▹ A ⊢? B ∋ b
... | yes Δ      = yes (C (lam Δ))
... | no         = no
Γ ⊢? A ⇒ B ∋C _  = no

Γ ⊢? nat ∋C ze  = yes (C ze)
Γ ⊢? nat ∋C su n
  with Γ ⊢? nat ∋ n
... | yes Δ     = yes (C (su Δ))
... | no        = no
Γ ⊢? nat ∋C _   = no

Γ ⊢? A + B ∋C inj₁ t
  with Γ ⊢? A ∋ t
... | yes Δ      = yes (C (inj₁ Δ))
... | no         = no
Γ ⊢? A + B ∋C inj₂ t
  with Γ ⊢? B ∋ t
... | yes Δ      = yes (C (inj₂ Δ))
... | no         = no
Γ ⊢? A + B ∋C _  = no


Γ ! nat ∋ Δt ⊢? A ∋# split fs fz
  with Γ ▹ A ⊢? A ∋ fs | Γ ⊢? A ∋ fz
... | yes Δfs | yes Δfz      = yes (Δt # iter Δfs Δfz)
... | yes Δfs | no           = no
... | no      | _            = no
Γ ! X + Y ∋ Δt ⊢? A ∋# split cX cY
  with (X ∷ Γ) ⊢? A ∋ cX | (Y ∷ Γ) ⊢? A ∋ cY
... | yes ΔcX | yes ΔcY      = yes (Δt # case ΔcX ΔcY)
... | yes ΔcX | no           = no
... | no      | _            = no
Γ ! _ ∋ _ ⊢? _ ∋# split _ _  = no

Γ ! A ⇒ B ∋ Δf ⊢? apply s ∈#
  with Γ ⊢? A ∋ s
... | yes Δs             = yes (Δf # apply Δs)
... | no                 = no
Γ ! _ ∋ _ ⊢? apply _ ∈#  = no

Γ ! A * B ∋ Δ ⊢? fst ∈#  = yes (Δ # fst)
Γ ! _ ∋ _ ⊢? fst ∈#      = no

Γ ! A * B ∋ Δ ⊢? snd ∈#  = yes (Δ # snd)
Γ ! _ ∋ _ ⊢? snd ∈#      = no

-- ** Tests

nat∋t1' : [] ⊢ nat ∋ t1
nat∋t1' = lemma ([] ⊢? nat ∋ t1) tt

T1 : type
T1 = nat ⇒ (unit + unit)

T2 : type
T2 = (nat + unit) ⇒ (unit + unit)

T1∋t2 : [] ⊢ T1 ∋ t2
T1∋t2 = lemma ([] ⊢? T1 ∋ t2) tt

T2∋t2 : [] ⊢ T2 ∋ t2
T2∋t2 = lemma ([] ⊢? T2 ∋ t2) tt

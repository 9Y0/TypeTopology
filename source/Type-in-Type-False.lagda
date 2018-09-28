28 September 2018.

This is an application of work of Ingo Blechschmidt (see the module
LavwereFPT) to show that type-in-type, Streicher's K-axiom, functional
and propositional extensionality are together impossible.

A universe closed under 𝟘, 𝟙, Π, Σ and identity type is enough to get
a contradiction.

In particular, W-types are not needed.

NB. We use the option without-K but then postulate K.

postulate K-axiom : (X : Set) → is-set X
postulate funext  : {X : Set} {A : X → Set} {f g : Π A} → f ∼ g → f ≡ g
postulate propext : {P Q : Set} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

NB. The universe of types is called Set in Agda. This terminology is
consistent with the K axiom.

We don't use any libraries, not even our own libraries, in order to
easily check which closure propeties of the universe are needed.

\begin{code}

{-# OPTIONS --without-K --type-in-type --exact-split #-}

module Type-in-Type-False where

\end{code}

We first define 𝟘, 𝟙, Σ and the identity type (written _≡_), and name
the predefined construction Π:

\begin{code}

data 𝟘 : Set where

data 𝟙 : Set where
 * : 𝟙

Π : {X : Set} (Y : X → Set) → Set
Π Y = (x : _) → Y x

record Σ {X : Set} (Y : X → Set) : Set where
  constructor _,_
  field
   pr₁ : X
   pr₂ : Y pr₁

open Σ public

_×_ : Set → Set → Set
X × Y = Σ \(x : X) → Y

data _≡_ {X : Set} : X → X → Set where
  refl : {x : X} → x ≡ x

\end{code}

Function identity and composition:

\begin{code}

id : {X : Set} → X → X
id x = x

_∘_ : {X Y : Set} {Z : Y → Set}
    → ((y : Y) → Z y) → (f : X → Y) → (x : X) → Z (f x)
g ∘ f = λ x → g(f x)

\end{code}

Equality basics:

\begin{code}

transport : {X : Set} (A : X → Set) {x y : X}
          → x ≡ y → A x → A y
transport A refl = id

ap : {X Y : Set} (f : X → Y) {x x' : X} → x ≡ x' → f x ≡ f x'
ap f p = transport (λ - → f _ ≡ f -) p refl

_⁻¹ : {X : Set} → {x y : X} → x ≡ y → y ≡ x
p ⁻¹ = transport (λ - → - ≡ _) p refl

_∙_ : {X : Set} {x y z : X} → x ≡ y → y ≡ z → x ≡ z
p ∙ q = transport (λ x → _ ≡ x) q p

to-Σ-≡ : {X : Set} {A : X → Set} {σ τ : Σ A}
       → (Σ \(p : pr₁ σ ≡ pr₁ τ) → transport A p (pr₂ σ) ≡ pr₂ τ)
       → σ ≡ τ
to-Σ-≡ (refl , refl) = refl

_∼_ : {X : Set} {A : X → Set} → Π A → Π A → Set
f ∼ g = (x : _) → f x ≡ g x

\end{code}

Function extensionality axiom:

\begin{code}

postulate funext : {X : Set} {A : X → Set} {f g : Π A} → f ∼ g → f ≡ g

\end{code}

Propositions and sets and the K axiom:

\begin{code}

is-prop : Set → Set
is-prop X = (x y : X) → x ≡ y

is-set : Set → Set
is-set X = {x y : X} → is-prop(x ≡ y)

postulate K-axiom : (X : Set) → is-set X

\end{code}

Because we are using type-in-type:

\begin{code}

Set-is-set : is-set Set
Set-is-set = K-axiom Set

is-prop-is-prop : {X : Set} → is-prop (is-prop X)
is-prop-is-prop {X} f g = funext (λ x → funext (c x))
 where
  c : (x y : X) → f x y ≡ g x y
  c x y = K-axiom X (f x y) (g x y)

Π-is-prop : {X : Set} {A : X → Set}
          → ((x : X) → is-prop (A x)) → is-prop (Π A)
Π-is-prop i f g = funext (λ x → i x (f x) (g x))

\end{code}

Propositional extensionality axiom:

\begin{code}

postulate propext : {P Q : Set} → is-prop P → is-prop Q → (P → Q) → (Q → P) → P ≡ Q

\end{code}

Because we have type-in-type and function extensionality, we can
define propositional truncations (following Voevodsky):

\begin{code}

∥_∥ : Set → Set
∥ X ∥ = (P : Set) → is-prop P → (X → P) → P

∥∥-is-prop : {X : Set} → is-prop ∥ X ∥
∥∥-is-prop {X} = Π-is-prop (λ P → Π-is-prop (λ i → Π-is-prop (λ u → i)))

∣_∣ : {X : Set} → X → ∥ X ∥
∣ x ∣ = λ P _ u → u x

∥∥-rec : {X P : Set} → is-prop P → (X → P) → ∥ X ∥ → P
∥∥-rec {X} {P} isp φ s = s P isp φ

Prop : Set
Prop = Σ \(P : Set) → is-prop P

_holds : Prop → Set
_holds = pr₁

holds-is-prop : (p : Prop) → is-prop (p holds)
holds-is-prop = pr₂

𝟘-is-prop : is-prop 𝟘
𝟘-is-prop ()

¬_ : Set → Set
¬ X = X → 𝟘

not : Prop → Prop
not (P , i) = (¬ P , Π-is-prop (λ x → 𝟘-is-prop))

\end{code}

Retracts and equivalences basics:

\begin{code}

has-section : {X Y : Set} → (X → Y) → Set
has-section r = Σ \s → r ∘ s ∼ id

retract_of_ : Set → Set → Set
retract Y of X = Σ \(r : X → Y) → has-section r

retracts-compose : {X Y Z : Set} → retract Y of X → retract Z of Y → retract Z of X
retracts-compose (r , (s , η)) (r' , (s' , η')) = r' ∘ r ,
                                                  (s ∘ s' ,
                                                  λ z → ap r' (η (s' z)) ∙ η' z)

Id-retract : {X Y : Set} → X ≡ Y → retract Y of X
Id-retract refl = id , id , (λ y → refl)

has-retraction : {X Y : Set} → (X → Y) → Set
has-retraction s = Σ \r → r ∘ s ∼ id

is-equiv : {X Y : Set} → (X → Y) → Set
is-equiv f = has-section f × has-retraction f

_≃_ : Set → Set → Set
X ≃ Y = Σ \(f : X → Y) → is-equiv f

idtoeq : (X Y : Set) → X ≡ Y → X ≃ Y
idtoeq X Y refl = id , (id , (λ (x : X) → refl)) , id , (λ (y : Y) → refl)

equiv-retract : {X Y : Set} → X ≃ Y → retract Y of X
equiv-retract (f , (g , fg) , (h , hf)) = f , g , fg

\end{code}

Having defined our basic type theory, postulated our axioms, and
developed some minimal machinery, we are ready to embark into our
proof of false.

Our main tool is Lawvere's fixed point theorem (formulated for
retractions rather than surjections, for simplicity, as this is
enough for us):

\begin{code}

LFPT : {A : Set} {X : Set}
     → retract (A → X) of A
     → (f : X → X) → Σ \(x : X) → x ≡ f x
LFPT {A} {X} (r , (s , η)) f = x , p
 where
  g : A → X
  g a = f (r a a)
  x : X
  x = r (s g) (s g)
  p : x ≡ f x
  p = ap (λ - → - (s g)) (η g)

LFPT-≡ : {A : Set} {X : Set}
       → A ≡ (A → X)
       → (f : X → X) → Σ \(x : X) → x ≡ f x
LFPT-≡ p = LFPT (Id-retract p)

\end{code}

A simple application is to show that negation doesn't have fixed
points:

\begin{code}

not-no-fp : ¬ Σ \(B : Prop) → B ≡ not B
not-no-fp (B , p) = pr₁(γ id)
 where
  q : B holds ≡ ¬(B holds)
  q = ap _holds p
  γ : (f : 𝟘 → 𝟘) → Σ \(x : 𝟘) → x ≡ f x
  γ = LFPT-≡ q

\end{code}

It is here that we need proposition extensionality in a crucial way:

\begin{code}

Π-projection-has-section :
   {X : Set} {Y : X → Set}
 → (x₀ : X) → has-section (λ (f : (x : X) → Y x → Prop) → f x₀)
Π-projection-has-section {X} {Y} x₀ = s , η
 where
  s : (Y x₀ → Prop) → ((x : X) → Y x → Prop)
  s φ x y = ∥(Σ \(p : x ≡ x₀) → φ (transport Y p y) holds)∥ , ∥∥-is-prop
  η : (φ : Y x₀ → Prop) → s φ x₀ ≡ φ
  η φ = funext γ
   where
    a : (y₀ : Y x₀) → ∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥ → φ y₀ holds
    a y₀ = ∥∥-rec (holds-is-prop (φ y₀)) f
     where
      f : (Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds) → φ y₀ holds
      f (p , h) = transport _holds t h
       where
        r : p ≡ refl
        r = K-axiom X p refl
        t : φ (transport Y p y₀) ≡ φ y₀
        t = ap (λ - → φ(transport Y - y₀)) r
    b : (y₀ : Y x₀) → φ y₀ holds → ∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥
    b y₀ h = ∣ refl , h ∣
    γ : (y₀ : Y x₀) → (∥(Σ \(p : x₀ ≡ x₀) → φ (transport Y p y₀) holds)∥ , ∥∥-is-prop) ≡ φ y₀
    γ y₀ = to-Σ-≡ (propext ∥∥-is-prop (holds-is-prop (φ y₀)) (a y₀) (b y₀) ,
                    is-prop-is-prop (holds-is-prop _) (holds-is-prop (φ y₀)) )

usr-lemma : {A : Set} (X : A → Set)
          → (a₀ : A)
          → retract ((a : A) → X a → Prop) of X a₀
          → (f : Prop → Prop) → Σ \(P : Prop) → P ≡ f P
usr-lemma {A} X a₀ retr = LFPT retr'
 where
  retr' : retract (X a₀ → Prop) of X a₀
  retr' = retracts-compose
           retr
           ((λ f → f a₀) , Π-projection-has-section a₀)

universe-regular-≃ : (A : Set) (X : A → Set) → Σ \(B : Set) → (a : A) → ¬(X a ≃ B)
universe-regular-≃ A X = B , φ
  where
   B : Set
   B = (a : A) → X a → Prop
   φ : (a : A) → ¬(X a ≃ B)
   φ a p = not-no-fp (γ not)
    where
     retr : retract B of (X a)
     retr = equiv-retract p
     γ : (f : Prop → Prop) → Σ \(P : Prop) → P ≡ f P
     γ = usr-lemma {A} X a retr

universe-regular : (A : Set) (X : A → Set) → Σ \(B : Set) → (a : A) → ¬(X a ≡ B)
universe-regular A X = γ (universe-regular-≃ A X)
 where
  γ : (Σ \(B : Set) → (a : A) → ¬(X a ≃ B))
    → (Σ \(B : Set) → (a : A) → ¬(X a ≡ B))
  γ (B , φ) = B , (λ a p → φ a (idtoeq (X a) B p))

families-do-not-have-sections : (A : Set) (X : A → Set) → ¬ has-section X
families-do-not-have-sections A X (s , η) = φ (s B) (η B)
 where
  B : Set
  B = pr₁ (universe-regular A X)
  φ : ∀ a → ¬(X a ≡ B)
  φ = pr₂ (universe-regular A X)

\end{code}

We now consider A = Set and X = id to get the desired contradiction,
as the identity function obviously does have a section, namely itself:

\begin{code}

contradiction : 𝟘
contradiction = families-do-not-have-sections Set id (id , (λ X → refl))

\end{code}

Question: Without assuming type-in-type, can we instead derive a
contradiction from the existence of a sufficiently large universe U
with X:U and X≃U?



Fixities and precedences:

\begin{code}

infixl 5 _∘_
infixr 4 _,_
infixr 2 _×_
infix  0 _≡_
infix  4  _∼_
infix  50 ¬_

\end{code}

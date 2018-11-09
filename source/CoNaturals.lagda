Martin Escardo 2012.

We investigate coinduction and corecursion on ℕ∞, the generic
convergent sequence.

We show that set ℕ∞ satisfies the following universal property for a
suitable coalgebra PRED : ℕ∞ → 𝟙 + ℕ∞, where 𝟙 is the singleton
type with an element *.

For every type X and every κ : X → 𝟙 + X there is a unique h : X → ℕ∞
such that

                        κ
             X ------------------> 𝟙 + X
             |                       |
             |                       |
          h  |                       | 𝟙 + h
             |                       |
             |                       |
             v                       v
             ℕ∞ -----------------> 𝟙 + ℕ∞
                       PRED

The maps κ and PRED are called coalgebras for the functor 𝟙 + (-),
and the above diagram says that h is a coalgebra morphism from p to
PRED.

In equational form, this is

             PRED ∘ h ≡ (𝟙 + h) ∘ κ,

which can be considered as a corecursive definition of h.  The map
PRED (a sort of predecessor function) is an isomorphism with
inverse SUCC (a sort of successor function). This follows from
Lambek's Lemma once the above universal property is established, but
we actually need to know this first in order to prove the universal
property.

             SUCC : 𝟙 + ℕ∞ → ℕ∞
             SUCC (in₀ *) = Zero
             SUCC (in₁ u) = Succ u

Using this fact, the above corecursive definition of h is equivalent
to:

             h ≡ SUCC ∘ (𝟙 + h) ∘ κ

or

             h(x) ≡ SUCC((𝟙 + h)(κ x)).

Now κ x is either of the form in₀ * or in₁ x' for a unique x' : X, and
hence the above equation amounts to

             h(x) ≡ Zero,           if κ x ≡ in₀ *,
             h(x) ≡ Succ (h x'),    if κ x ≡ in₁ x',

once we know the definition of 𝟙 + h. This shows more clearly how the
diagram can be considered as a (co)recursive definition of h, and
indicates how h may be constructed.

In order to show that any two functions that make the above diagram
commute are unique, that is, that the above two conditional equations
uniquely determine h, we develop a coinduction principle based on
bisimulations. This gives a technique for establishing equalities on
ℕ∞.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module CoNaturals (fe : ∀ U V → funext U V) where

open import SpartanMLTT
open import Two
open import GenericConvergentSequence

Zero' : 𝟙 + ℕ∞
Zero' = inl {U₀} {U₀} *

Pred' : ℕ∞ → 𝟙 + ℕ∞
Pred' u = inr {U₀} {U₀} (Pred u)

PRED : ℕ∞ → 𝟙 + ℕ∞
PRED u = 𝟚-Cases (positivity u) Zero' (Pred' u)

PRED-Zero : PRED Zero ≡ Zero'
PRED-Zero = refl

PRED-Succ : (u : ℕ∞) → PRED(Succ u) ≡ inr u
PRED-Succ u = ap inr Pred-Succ

SUCC : 𝟙 {U₀} + ℕ∞ → ℕ∞
SUCC(inl *) = Zero
SUCC(inr u) = Succ u

PRED-SUCC : {y : 𝟙 + ℕ∞} → PRED(SUCC y) ≡ y
PRED-SUCC{inl *} = refl
PRED-SUCC{inr u} = refl

SUCC-lc : {y z : 𝟙 + ℕ∞} → SUCC y ≡ SUCC z → y ≡ z
SUCC-lc r = PRED-SUCC ⁻¹ ∙ ap PRED r ∙ PRED-SUCC

SUCC-PRED : {u : ℕ∞} → SUCC(PRED u) ≡ u
SUCC-PRED {u} = 𝟚-equality-cases l₀ l₁
 where
  l₀ : positivity u ≡ ₀ → SUCC(PRED u) ≡ u
  l₀ r = c₁ ∙ (is-Zero-equal-Zero (fe U₀ U₀) r)⁻¹
    where
     c₀ : PRED u ≡ Zero'
     c₀ = ap (𝟚-cases Zero' (Pred' u)) r
     c₁ : SUCC(PRED u) ≡ Zero
     c₁ = ap SUCC c₀
  l₁ : positivity u ≡ ₁ → SUCC(PRED u) ≡ u
  l₁ r = c₁ ∙ c₃ ⁻¹
   where
     c₀ : PRED u ≡ Pred' u
     c₀ = ap (𝟚-cases Zero' (Pred' u)) r
     c₁ : SUCC(PRED u) ≡ Succ (Pred u)
     c₁ = ap SUCC c₀
     c₂ : u ≢ Zero
     c₂ s = Lemma[b≡₀→b≢₁](ap positivity s) r
     c₃ : u ≡ Succ (Pred u)
     c₃ = not-Zero-is-Succ (fe U₀ U₀) c₂

PRED-lc : {u v : ℕ∞} → PRED u ≡ PRED v → u ≡ v
PRED-lc r = SUCC-PRED ⁻¹ ∙ ap SUCC r ∙ SUCC-PRED

𝟙+ : {X : U ̇} {Y : V ̇} → (X → Y) → 𝟙 + X → 𝟙 + Y
𝟙+ f (inl s) = inl {U₀} s
𝟙+ f (inr x) = inr(f x)

𝟙+id-is-id : {X : U ̇} → 𝟙+ id ∼ id {U} {𝟙 + X}
𝟙+id-is-id {U} {X} (inl *) = refl
𝟙+id-is-id {U} {X} (inr x) = refl

is-homomorphism : {X : U ̇} → (X → 𝟙 + X) → (X → ℕ∞) → U ̇
is-homomorphism c h = (PRED ∘ h ≡ (𝟙+ h) ∘ c)

id-homomorphism : is-homomorphism PRED id
id-homomorphism = dfunext (fe U₀ U₀) (λ u → (𝟙+id-is-id (PRED u))⁻¹)

coalg-mophism→ : {X : U ̇} (κ : X → 𝟙 + X) (h : X → ℕ∞)
               → is-homomorphism κ h
               → h ≡ SUCC ∘ (𝟙+ h) ∘ κ
coalg-mophism→ {U} κ h a = dfunext (fe U U₀)
                             (λ x → SUCC-PRED ⁻¹ ∙ ap (λ - → SUCC(- x)) a)

coalg-mophism← : {X : U ̇} (κ : X → 𝟙 + X) (h : X → ℕ∞)
               → h ≡ SUCC ∘ (𝟙+ h) ∘ κ
               → is-homomorphism κ h
coalg-mophism← {U} κ h b = dfunext (fe U U₀)
                            (λ x → ap (λ - → PRED(- x)) b ∙ PRED-SUCC)

homomorphism-existence : {X : U ̇} (κ : X → 𝟙 + X)
                       → Σ \(h : X → ℕ∞) → is-homomorphism κ h
homomorphism-existence {U} {X} κ = h , dfunext (fe U U₀) h-spec
 where
  q : 𝟙 + X → 𝟙 + X
  q(inl s) = inl s
  q(inr x) = κ x

  Q : ℕ → 𝟙 + X → 𝟙 + X
  Q 0 z = z
  Q(succ n) z = q(Q n z)

  E : 𝟙 + X → 𝟚
  E(inl s) = ₀
  E(inr x) = ₁

  hl : (z : 𝟙 + X) → E(q z) ≡ ₁ → E z ≡ ₁
  hl (inl s) r = r
  hl (inr x) r = refl

  h : X → ℕ∞
  h x = ((λ i → E(Q(succ i) (inr x))) ,
          λ i → hl(Q(succ i) (inr x)))

  h-spec : (x : X) → PRED(h x) ≡ (𝟙+ h)(κ x)
  h-spec x = equality-cases (κ x) l₀ l₁
   where
    l₀ : (s : 𝟙) → κ x ≡ inl s → PRED(h x) ≡ (𝟙+ h)(κ x)
    l₀ * r = c₂ ∙ c₀ ⁻¹
     where
      c₀ : (𝟙+ h)(κ x) ≡ Zero'
      c₀ = ap (𝟙+ h) r
      c₁ : h x ≡ Zero
      c₁ = is-Zero-equal-Zero (fe U₀ U₀) (ap E r)
      c₂ : PRED(h x) ≡ Zero'
      c₂ = ap PRED c₁ ∙ PRED-Zero

    l₁ : (x' : X) → κ x ≡ inr x' → PRED(h x) ≡ (𝟙+ h)(κ x)
    l₁ x' r = c₆ ∙ c₀ ⁻¹
     where
      c₀ : (𝟙+ h)(κ x) ≡ inr(h x')
      c₀ = ap (𝟙+ h) r
      c₁ : (n : ℕ) → q(Q n (inr x)) ≡ Q n (κ x)
      c₁ 0 = refl
      c₁ (succ n) = ap q (c₁ n)
      c₂ : (n : ℕ) → q(Q n (inr x)) ≡ Q n (inr x')
      c₂ n = c₁ n ∙ ap (Q n) r
      c₃ : (n : ℕ) → E(q(Q n (inr x))) ≡ E(Q n (inr x'))
      c₃ n = ap E (c₂ n)
      c₄ : (i : ℕ) → incl(h x) i ≡ incl(Succ (h x')) i
      c₄ 0  = c₃ 0
      c₄ (succ i) = c₃(succ i)
      c₅ : h x ≡ Succ (h x')
      c₅ = incl-lc (fe U₀ U₀) (dfunext (fe U₀ U₀) c₄)

      c₆ : PRED(h x) ≡ inr(h x')
      c₆ = ap PRED c₅

ℕ∞-corec  : {X : U ̇} → (X → 𝟙 + X) → (X → ℕ∞)
ℕ∞-corec c = pr₁(homomorphism-existence c)

ℕ∞-corec-homomorphism : {X : U ̇} (κ : X → 𝟙 + X)
                      → is-homomorphism κ (ℕ∞-corec κ)
ℕ∞-corec-homomorphism κ = pr₂(homomorphism-existence κ)

\end{code}

We now discuss coinduction. We first define bisimulations.

\begin{code}

ℕ∞-bisimulation :(ℕ∞ → ℕ∞ → U ̇) → U ̇
ℕ∞-bisimulation R = (u v : ℕ∞) → R u v
                                → (positivity u ≡ positivity v)
                                ×  R (Pred u) (Pred v)

ℕ∞-coinduction : (R : ℕ∞ → ℕ∞ → U ̇) → ℕ∞-bisimulation R
               → (u v : ℕ∞) → R u v → u ≡ v
ℕ∞-coinduction R b u v r = incl-lc (fe U₀ U₀) (dfunext (fe U₀ U₀) (l u v r))
 where
  l : (u v : ℕ∞) → R u v → (i : ℕ) → incl u i ≡ incl v i
  l u v r 0 =  pr₁(b u v r)
  l u v r (succ i) = l (Pred u) (Pred v) (pr₂(b u v r)) i

\end{code}

To be able to use it for our purpose, we need to investigate
coalgebra homomorphisms in more detail.

\begin{code}

coalg-morphism-Zero : {X : U ̇} (κ : X →  𝟙 + X) (h : X → ℕ∞)
                    → is-homomorphism κ h
                    → (x : X) (s : 𝟙) → κ x ≡ inl s → h x ≡ Zero
coalg-morphism-Zero p h a x * κ = SUCC-PRED ⁻¹ ∙ ap SUCC c₃
 where
  c₁ : PRED(h x) ≡ (𝟙+ h)(p x)
  c₁ = ap (λ - → - x) a
  c₂ : (𝟙+ h)(p x) ≡ Zero'
  c₂ = ap (𝟙+ h) κ
  c₃ : PRED(h x) ≡ inl *
  c₃ = c₁ ∙ c₂

Coalg-morphism-Zero : {X : U ̇} (κ : X →  𝟙 + X)
                    → (x : X) (s : 𝟙) → κ x ≡ inl s → ℕ∞-corec κ x ≡ Zero
Coalg-morphism-Zero κ = coalg-morphism-Zero κ (ℕ∞-corec κ) (ℕ∞-corec-homomorphism κ)

coalg-morphism-Succ : {X : U ̇}
                      (κ : X →  𝟙 + X) (h : X → ℕ∞)
                    → is-homomorphism κ h
                    → (x x' : X) → κ x ≡ inr x' → h x ≡ Succ (h x')
coalg-morphism-Succ κ h a x x' q = SUCC-PRED ⁻¹ ∙ ap SUCC c₃
 where
  c₁ : PRED(h x) ≡ (𝟙+ h)(κ x)
  c₁ = ap (λ - → - x) a
  c₂ : (𝟙+ h)(κ x) ≡ inr(h x')
  c₂ = ap (𝟙+ h) q
  c₃ : PRED(h x) ≡ inr(h x')
  c₃ = c₁ ∙ c₂

Coalg-morphism-Succ : {X : U ̇} (κ : X →  𝟙 + X)
                    → (x x' : X) → κ x ≡ inr x' → ℕ∞-corec κ x ≡ Succ (ℕ∞-corec κ x')
Coalg-morphism-Succ κ = coalg-morphism-Succ κ (ℕ∞-corec κ) (ℕ∞-corec-homomorphism κ)

\end{code}

The following two technical lemmas are used to construct a
bisimulation:

\begin{code}

coalg-morphism-positivity : {X : U ̇}
                            (κ : X →  𝟙 + X) (f g : X → ℕ∞)
                          → is-homomorphism κ f
                          → is-homomorphism κ g
                          → (x : X) → positivity(f x) ≡ positivity(g x)
coalg-morphism-positivity {U} {X} κ f g a b x =
 equality-cases (κ x) l₀ l₁
 where
  l₀ : (s : 𝟙) → κ x ≡ inl s → positivity(f x) ≡ positivity(g x)
  l₀ s q = fl ∙ gl ⁻¹
   where
    fl : positivity(f x) ≡ ₀
    fl = ap positivity(coalg-morphism-Zero κ f a x s q)
    gl : positivity(g x) ≡ ₀
    gl = ap positivity(coalg-morphism-Zero κ g b x s q)

  l₁ : (x' : X) → κ x ≡ inr x' → positivity(f x) ≡ positivity(g x)
  l₁ x' q = fl ∙ gl ⁻¹
   where
    fl : positivity(f x) ≡ ₁
    fl = ap positivity(coalg-morphism-Succ κ f a x x' q)
    gl : positivity(g x) ≡ ₁
    gl = ap positivity(coalg-morphism-Succ κ g b x x' q)

coalg-morphism-Pred : {X : U ̇}
                      (κ : X →  𝟙 + X) (f g : X → ℕ∞)
                    → is-homomorphism κ f
                    → is-homomorphism κ g
                    → (x : X) (u v : ℕ∞)
                    → u ≡ f x
                    → v ≡ g x
                    → Σ \(x' : X) → (Pred u ≡ f x') × (Pred v ≡ g x')
coalg-morphism-Pred {U} {X} κ f g a b x u v d e =
 equality-cases (κ x) l₀ l₁
 where
  l₀ : (s : 𝟙) → κ x ≡ inl s
     → Σ \x' → (Pred u ≡ f x') ×  (Pred v ≡ g x')
  l₀ s q = x , (l f a u d , l g b v e)
   where
    l : (h : X → ℕ∞) → PRED ∘ h ≡ (𝟙+ h) ∘ κ
      → (u : ℕ∞) → u ≡ h x → Pred u ≡ h x
    l h a u d = c₁ ∙ c₀ ⁻¹
     where
      c₀ : h x ≡ Zero
      c₀ = coalg-morphism-Zero κ h a x s q
      c₁ : Pred u ≡ Zero
      c₁ = ap Pred (d ∙ c₀)

  l₁ : (x' : X) → κ x ≡ inr x'
     → Σ \x' → (Pred u ≡ f x') × (Pred v ≡ g x')
  l₁ x' q = x' , (l f a u d , l g b v e)
   where
    l : (h : X → ℕ∞) → PRED ∘ h ≡ (𝟙+ h) ∘ κ
      → (u : ℕ∞) → u ≡ h x → Pred u ≡ h x'
    l h a u d = ap Pred d ∙ l'
     where
      l' : Pred(h x) ≡ h x'
      l' = ap Pred(coalg-morphism-Succ κ h a x x' q)

\end{code}

We are finally able to prove the uniqueness of coalgebra homomorphisms
from p to PRED.

\begin{code}

homomorphism-uniqueness : {X : U ̇}
                          (κ : X → 𝟙 + X) (f g : X → ℕ∞)
                        → is-homomorphism κ f
                        → is-homomorphism κ g
                        → f ≡ g
homomorphism-uniqueness {U} {X} κ f g a b = dfunext (fe U U₀) l
 where
  R : ℕ∞ → ℕ∞ → U ̇
  R u v = Σ \x → (u ≡ f x) × (v ≡ g x)

  r : (x : X) → R (f x) (g x)
  r x = (x , refl , refl)

  R-positivity : (u v : ℕ∞) → R u v → positivity u ≡ positivity v
  R-positivity u v (x , c , d) = ap positivity c ∙ e ∙ ap positivity (d ⁻¹)
   where
    e : positivity(f x) ≡ positivity(g x)
    e = coalg-morphism-positivity {U} {X} κ f g a b x

  R-Pred : (u v : ℕ∞) → R u v → R (Pred u) (Pred v)
  R-Pred u v (x , c , d) =
   (pr₁ l , pr₁(pr₂ l) , pr₂(pr₂ l))
   where
    l : Σ \x' → (Pred u ≡ f x') × (Pred v ≡ g x')
    l = coalg-morphism-Pred κ f g a b x u v c d

  R-bisimulation : ℕ∞-bisimulation R
  R-bisimulation u v r = (R-positivity u v r) , (R-Pred u v r)

  l : f ∼ g
  l x = ℕ∞-coinduction R R-bisimulation (f x) (g x) (r x)

\end{code}

Putting existence and uniqueness together, we get that PRED is the final
coalgebra, as claimed:

\begin{code}

PRED-is-the-final-coalgebra : {X : U ̇}
  → (κ : X → 𝟙 + X) → Σ! \(h : X → ℕ∞) → is-homomorphism κ h
PRED-is-the-final-coalgebra κ = homomorphism-existence κ , homomorphism-uniqueness κ

\end{code}

There is more formalization work to do (2017): By now we know that Σ!
(a form of unique existence) is better captured by the contractibility
of Σ type (added 13th July 2018):

\begin{code}

open import UF-Base
open import UF-Subsingletons
open import UF-Subsingletons-FunExt

PRED-is-the-homotopy-final-coalgebra : {X : U ̇} (κ : X → 𝟙 + X)
  → is-singleton(Σ \(h : X → ℕ∞) → is-homomorphism κ h)
PRED-is-the-homotopy-final-coalgebra {U} {X} κ = homomorphism-existence κ , γ
 where
  γ : (e : Σ \(h' : X → ℕ∞) → is-homomorphism κ h') → homomorphism-existence κ ≡ e
  γ (h' , r) = to-Σ-≡
                (homomorphism-uniqueness κ (ℕ∞-corec κ) h' (ℕ∞-corec-homomorphism κ) r ,
                 Π-is-set (fe U U₀)
                   (λ _ → +-is-set 𝟙 ℕ∞
                           (props-are-sets 𝟙-is-prop)
                           (ℕ∞-is-set (fe U₀ U₀))) _ _)

\end{code}

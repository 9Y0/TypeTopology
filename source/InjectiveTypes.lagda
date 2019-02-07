Martin Escardo, 27 April 2014, with later additions, 2017, 2018, 2019.

This introduction is incomplete and outdated.

We show that the injective types are the retracts of the exponential
powers of universes, where an exponential power of a type D is a type
of the form A → D for some type A. Injectivity is defined as
(functional) data rather than property.


Injectivity of the universe (2014)
----------------------------

Here we have definitions and proofs in Agda notation, which assume a
univalent mathematics background (e.g. given by the HoTT book),
preceded by informal (rigorous) discussion.

We show that the universe is (right-Kan) injective wrt embeddings. An
embedding is a map j:X→Y whose fibers are all univalent propositions.

In the remote past, I looked at injectivity in categories of spaces
and locales, with respect to various kinds of maps, and I wrote
several papers about that.

At present, I am looking at searchable sets in type theory
(corresponding to compact sets in topology), and I accidentally landed
in the same injectivity territory. This file is about
injectivity. Other files make use of this for searchability purposes,
which is not discussed here.

Abstractly, the general situation is

                   j
              X ------> Y
               \       /
                \     /
             f   \   / f/j
                  \ /
                   v
                   D

Given f and j, we want to find f/j making the diagram commute (that
is, f = f/j ∘ j). Of course, this "extension property" is not always
possible, and it depends on properties of f, j and D. Usually, one
requires j to be an embedding (of some sort).

Here I consider the case that D=𝓤, a universe, in which case, if one
doesn't want to assume univalence, then it makes sense to consider
commutation up to equivalence:

                   j
              X ------> Y
               \       /
                \  ≃  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

But this can be the case only if j is an embedding in a suitable
sense. Otherwise, we only have a right-Kan extension

                   j
              X ------> Y
               \       /
                \  ≳  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

in the sense that the type of natural transformations from "presheaves"
g : Y → 𝓤 to the "presheaf" f/j, written

     g ≾ f/j,

is naturally equivalent to the type g∘j ≾ f of natural
transformations from g∘j to f:

     g ≾ f/j ≃ g∘j ≾ f

If j is an embedding (in the sense of univalent mathematics), then,
for any f, we can find f/j which is both a right-Kan extension and a
(proper) extension (up to equivalence).

All this dualizes with Π replaced by Σ and right replaced by left.

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

open import UF-FunExt

module InjectiveTypes (fe : FunExt) where

open import SpartanMLTT
open import UF-Base
open import UF-Equiv
open import UF-Embeddings
open import UF-Retracts
open import UF-EquivalenceExamples
open import UF-Univalence
open import UF-IdEmbedding
open import UF-PropIndexedPiSigma
open import UF-Subsingletons
open import UF-Resizing
open import UF-PropTrunc
open import UF-UniverseEmbedding
open import UF-ExcludedMiddle

\end{code}

Here is how we define f/j given f and j.

                   j
              X ------> Y
               \       /
                \  ≳  /
             f   \   / f/j
                  \ /
                   v
                   𝓤

We have to apply the following constructions for 𝓤=𝓥=𝓦 for the above
triangles to make sense.

We rename the type of natural transformations:

\begin{code}

_≾_ : {X : 𝓤 ̇} → (X → 𝓥 ̇) → (X → 𝓦 ̇) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
_≾_ = Nat

_≾_-explicitly : {X : 𝓤 ̇} (A : X → 𝓥 ̇) (B : X → 𝓦 ̇)
               → A ≾ B ≡ ((x : X) → A x → B x)
_≾_-explicitly A B = refl

module _ {X : 𝓤 ̇}
         {Y : 𝓥 ̇}
         (f : X → 𝓦 ̇)
         (j : X → Y)
       where

  Π-extension Σ-extension : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
  Π-extension y = Π \(w : fiber j y) → f(pr₁ w)
  Σ-extension y = Σ \(w : fiber j y) → f(pr₁ w)

  private
   f/j f∖j : Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
   f/j = Π-extension
   f∖j = Σ-extension

  Σ→Π : is-embedding j → f∖j ≾ f/j
  Σ→Π e y ((x , p) , B) (x' , p') = transport f (embedding-lc j e (p ∙ p' ⁻¹)) B

\end{code}

  The natural transformation Σ→Π j itself should be a natural
  embedding (conjectural conjecture).

\begin{code}

  ηΠ : f/j ∘ j ≾ f
  ηΠ x C = C(x , refl)

  ηΣ : f ≾ f∖j ∘ j
  ηΣ x B = (x , refl) , B

\end{code}

  For arbitrary j:X→Y, this gives Kan extensions in the following
  sense:

\begin{code}

  Π-extension-right-Kan : (g : Y → 𝓣 ̇) → (g ≾ f/j) ≃  (g ∘ j ≾ f)
  Π-extension-right-Kan {𝓣} g = qinveq (ψ g) (φ g , φψ' g , ψφ' g)
   where
    φ : (g : Y → 𝓣 ̇) → g ∘ j ≾ f → g ≾ f/j
    φ g η y C (x , p) = η x (back-transport g p C)

    ψ : (g : Y → 𝓣 ̇) → g ≾ f/j → g ∘ j ≾ f
    ψ g θ x C = θ (j x) C (x , refl)

    ψφ : (g : Y → 𝓣 ̇) (η : g ∘ j ≾ f) (x : X) (C : g (j x)) → ψ g (φ g η) x C ≡ η x C
    ψφ g η x C = refl

    ψφ' : (g : Y → 𝓣 ̇) (η : g ∘ j ≾ f) → ψ g (φ g η) ≡ η
    ψφ' g η = dfunext (fe 𝓤 (𝓦 ⊔ 𝓣)) (λ x → dfunext (fe 𝓣 𝓦) (ψφ g η x))

    φψ : (g : Y → 𝓣 ̇) (θ : g ≾ f/j) (y : Y) (C : g y) (w : fiber j y) → φ g (ψ g θ) y C w ≡ θ y C w
    φψ g θ y C (x , refl) = refl

    φψ' : (g : Y → 𝓣 ̇) (θ : g ≾ f/j) → φ g (ψ g θ) ≡ θ
    φψ' g θ = dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)) (λ y → dfunext (fe 𝓣 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ C → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (φψ g θ y C)))

  Σ-extension-left-Kan : (g : Y → 𝓣 ̇) → (f∖j ≾ g) ≃ (f ≾ g ∘ j)
  Σ-extension-left-Kan {𝓣} g = e
   where
    φ : (g : Y → 𝓣 ̇) → f ≾ g ∘ j → f∖j ≾ g
    φ g η y ((x , p) , C) = transport g p (η x C)

    ψ : (g : Y → 𝓣 ̇) → f∖j ≾ g → f ≾ g ∘ j
    ψ g θ x B = θ (j x) ((x , refl) , B)

    φψ : (g : Y → 𝓣 ̇) (θ : f∖j ≾ g) (y : Y) (B : f∖j y) → φ g (ψ g θ) y B ≡ θ y B
    φψ g θ y ((x , refl) , B) = refl

    ψφ : (g : Y → 𝓣 ̇) (η : f ≾ g ∘ j) (x : X) (B : f x) → ψ g (φ g η) x B ≡ η x B
    ψφ g η x B = refl

    e : f∖j ≾ g ≃ f ≾ g ∘ j
    e = ψ g , (φ g , λ η → dfunext (fe 𝓤 (𝓦 ⊔ 𝓣)) (λ x → dfunext (fe 𝓦 𝓣) (λ B → ψφ g η x B)))
            , (φ g , λ θ → dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦 ⊔ 𝓣)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥 ⊔ 𝓦) 𝓣) (λ C → φψ g θ y C)))

\end{code}

  Conjectural conjecture: the type

    Σ(f' : Y → 𝓤), Π(g : Y → 𝓤), g ≾ f' ≃ g∘j ≾ f

  should be contractible assuming univalence. Similarly for left Kan
  extensions as discussed below.

  The above formula actually give extensions up to pointwise
  equivalence if j:X→Y is an embedding in the sense of univalent
  mathematics.

\begin{code}

  Π-extension-in-range : is-embedding j → (x : X) → f/j(j x) ≃ f x
  Π-extension-in-range e x = prop-indexed-product (fe (𝓤 ⊔ 𝓥) 𝓦) {fiber j (j x)} {λ (z : fiber j (j x)) → f (pr₁ z)} (e (j x)) (x , refl)

  Π-extension-equivalence : is-embedding j → (x : X) → is-equiv (Π-proj (x , refl))
  Π-extension-equivalence e x = pr₂ (Π-extension-in-range e x)

  Π-extension-out-of-range : ∀ {𝓦} (y : Y) → ((x : X) → j x ≢ y) → f/j(y) ≃ 𝟙 {𝓦}
  Π-extension-out-of-range y φ = prop-indexed-product-one (fe (𝓤 ⊔ 𝓥) 𝓦) (uncurry φ)

  Σ-extension-in-range : is-embedding j → (x : X) → f∖j(j x) ≃ f x
  Σ-extension-in-range e x = prop-indexed-sum (e(j x)) (x , refl)

  Σ-extension-out-of-range : (y : Y) → ((x : X) → j x ≢ y) → f∖j(y) ≃ 𝟘 {𝓦}
  Σ-extension-out-of-range y φ = prop-indexed-sum-zero (uncurry φ)

\end{code}

  We now rewrite the Π-extension formula in an equivalent way:

\begin{code}

  2nd-Π-extension-formula : (y : Y) → f/j(y) ≃ Π \(x : X) → j x ≡ y → f x
  2nd-Π-extension-formula y = curry-uncurry fe

  2nd-Π-extension-formula' : (y : Y) → f/j(y) ≃ (λ x → j x ≡ y) ≾ f
  2nd-Π-extension-formula' = 2nd-Π-extension-formula

  2nd-Σ-extension-formula : (y : Y) → f∖j(y) ≃ Σ \(x : X) → (j x ≡ y) × f x
  2nd-Σ-extension-formula y = Σ-assoc


\end{code}

  This is the Π-extension formula we actually used for (1) showing that
  the universe is indiscrete, and (2) defining the squashed sum and
  proving that it preserves searchability.

\begin{code}

  Π-observation : is-embedding j → (a : X) → f a ≃ (Π \(x : X) → j x ≡ j a → f x)
  Π-observation e a = ≃-sym ((≃-sym (2nd-Π-extension-formula (j a))) ●
                                      (Π-extension-in-range e a))

  Σ-observation : is-embedding j → (a : X) → f a ≃ (Σ \(x : X) → (j x ≡ j a) × f x)
  Σ-observation e a = ≃-sym ((≃-sym (2nd-Σ-extension-formula (j a))) ●
                                      (Σ-extension-in-range e a))

\end{code}

Added December 2017:

The extensions f/j and f∖j have the same product and sum as f
respectively:

\begin{code}

  same-Π : Π f ≃ Π f/j
  same-Π = F , (G , FG) , (G , GF)
    where
      F : Π f → Π f/j
      F φ y (x , p) = φ x

      G : Π f/j → Π f
      G ψ x = ψ (j x) (x , refl)

      FG' : (ψ : Π f/j) (y : Y) (σ : fiber j y) → F(G ψ) y σ ≡ ψ y σ
      FG' ψ x (_ , refl) = refl

      FG : (ψ : Π f/j) → F(G ψ) ≡ ψ
      FG ψ = dfunext (fe 𝓥 (𝓤 ⊔ 𝓥 ⊔ 𝓦)) (λ y → dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (FG' ψ y))

      GF : (φ : Π f) → G(F φ) ≡ φ
      GF φ = refl

  same-Σ : Σ f ≃ Σ f∖j
  same-Σ = F , (G , FG) , (G , GF)
    where
      F : Σ f → Σ f∖j
      F (x , y) = (j x , (x , refl) , y)

      G : Σ f∖j → Σ f
      G (y , (x , p) , y') = (x , y')

      FG : (σ : Σ f∖j) → F(G σ) ≡ σ
      FG (x , (_ , refl) , y') = refl

      GF : (σ : Σ f) → G(F σ) ≡ σ
      GF (x , y) = refl

\end{code}

(Conjectural conjecture (2nd July 2018): if j is an embedding, then we
have an embedding Σ f → Σ f/j.)

We now introduce the notations f / j and f ∖ j for the Π- and
Σ-extensions, outside the above anonymous module.

\begin{code}

_/_ _∖_ :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
        → (X → 𝓦 ̇) → (X → Y) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇)
f / j = Π-extension f j
f ∖ j = Σ-extension f j

infix 7 _/_

\end{code}

Also added December 2017.

A different notation reflects a different view of these processes:

\begin{code}

inverse-image :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
              → (X → Y) → (Y → 𝓦 ̇) → (X → 𝓦 ̇)

inverse-image f v = v ∘ f


Π-image Σ-image :  {X : 𝓤 ̇} {Y : 𝓥 ̇}
                → (X → Y) → ((X → 𝓦 ̇) → (Y → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇))

Π-image j = λ f → Π-extension f j

Σ-image j = λ f → Σ-extension f j

\end{code}

Σ-images of singletons. Another way to see the following is with the
function same-Σ defined above. This and univalence give

 Σ (Id x) ≡ Σ (Id x ∖ j) = Σ-image j (Id x)

Hence

 is-singleton(Σ (Id x)) ≡ is-singleton(Σ-image j (Id x))

But the lhs holds, and hence is-singleton(Σ-image j (Id x)).

\begin{code}

Σ-image-of-singleton-lemma : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (j : X → Y) (x : X) (y : Y)
                           → Σ-image j (Id x) y ≃ Id (j x) y
Σ-image-of-singleton-lemma {𝓤} {𝓥} {X} {Y} j x y = (f , (g , fg) , (g , gf))
 where
  f : Σ-image j (Id x) y → Id (j x) y
  f ((x , refl) , refl) = refl

  g : Id (j x) y → Σ-image j (Id x) y
  g refl = (x , refl) , refl

  gf : (i : Σ-image j (Id x) y) → g(f i) ≡ i
  gf ((x , refl) , refl) = refl

  fg : (p : Id (j x) y) → f(g p) ≡ p
  fg refl = refl

Σ-image-of-singleton-lemma' : {X : 𝓤 ̇} {Y : 𝓥 ̇} → (j : X → Y) (x : X) (y : Y)
                            → (((Id x) ∖ j) y) ≃ (j x ≡ y)
Σ-image-of-singleton-lemma' = Σ-image-of-singleton-lemma

Σ-image-of-singleton : {X Y : 𝓤 ̇}
                     → is-univalent 𝓤
                     → (j : X → Y) (x : X) → Σ-image j (Id x) ≡ Id (j x)
Σ-image-of-singleton {𝓤} {X} {Y} ua j x = b
  where
   a : (y : Y) → Σ-image j (Id x) y ≡ Id (j x) y
   a y = eqtoid ua (Σ-image j (Id x) y) (Id (j x) y) (Σ-image-of-singleton-lemma j x y)

   b : Σ-image j (Id x) ≡ Id (j x)
   b = dfunext (fe 𝓤 (𝓤 ⁺)) a

Σ-image-of-singleton' : {X Y : 𝓤 ̇}
                      → is-univalent 𝓤
                      → (j : X → Y) (x : X) → (Id x) ∖ j ≡ Id (j x)
Σ-image-of-singleton' = Σ-image-of-singleton

\end{code}

There is more to do about this.

\begin{code}

Π-extension-is-extension : is-univalent (𝓤 ⊔ 𝓥) → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                         → is-embedding j
                         → (f : X → 𝓤 ⊔ 𝓥 ̇) → (f / j) ∘ j ∼ f
Π-extension-is-extension ua j e f x = eqtoid ua _ _ (Π-extension-in-range f j e x)

Π-extension-is-extension' : is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                          → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                          → is-embedding j
                          → (f : X → 𝓤 ⊔ 𝓥 ̇) → (f / j) ∘ j ≡ f
Π-extension-is-extension' ua fe j e f = dfunext fe (Π-extension-is-extension ua j e f)

Π-extension-is-extension'' : is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺) → funext ((𝓤 ⊔ 𝓥)⁺) ((𝓤 ⊔ 𝓥)⁺)
                           → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                           → is-embedding j
                           → (λ f → (f / j) ∘ j) ≡ id
Π-extension-is-extension'' ua fe fe' j e = dfunext fe' (Π-extension-is-extension' ua fe j e)

Σ-extension-is-extension : is-univalent (𝓤 ⊔ 𝓥) → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                         → is-embedding j
                         → (f : X → 𝓤 ⊔ 𝓥 ̇) → (f ∖ j) ∘ j ∼ f
Σ-extension-is-extension ua j e f x = eqtoid ua _ _ (Σ-extension-in-range f j e x)

Σ-extension-is-extension' : is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺)
                          → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                          → is-embedding j
                          → (f : X → 𝓤 ⊔ 𝓥 ̇) → (f ∖ j) ∘ j ≡ f
Σ-extension-is-extension' ua fe j e f = dfunext fe (Σ-extension-is-extension ua j e f)

Σ-extension-is-extension'' : is-univalent (𝓤 ⊔ 𝓥) → funext 𝓤 ((𝓤 ⊔ 𝓥)⁺) → funext ((𝓤 ⊔ 𝓥)⁺) ((𝓤 ⊔ 𝓥)⁺)
                           → {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y)
                           → is-embedding j
                           → (λ f → (f ∖ j) ∘ j) ≡ id
Σ-extension-is-extension'' ua fe fe' j e = dfunext fe' (Σ-extension-is-extension' ua fe j e)

\end{code}

We now consider injectivity, defined with Σ rather than ∃ (that is, as
data rather than property):

\begin{code}

injective_over_ : 𝓦 ̇ → {X : 𝓤 ̇} {Y : 𝓥 ̇} → (X → Y) → 𝓤 ⊔ 𝓥 ⊔ 𝓦 ̇
injective D over j = (f : domain j → D) → Σ \(f' : codomain j → D) → f' ∘ j ∼ f

injective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
injective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                      → injective D over j

embedding-retract : (D : 𝓦 ̇) (Y : 𝓥 ̇) (j : D → Y) → is-embedding j → injective-type D 𝓦 𝓥
                  → retract D of Y
embedding-retract D Y j e i = pr₁ a , j , pr₂ a
 where
  a : Σ \(f' : Y → D) → f' ∘ j ∼ id
  a = i j e id

universes-are-injective-Π : is-univalent (𝓤 ⊔ 𝓥) → injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective-Π ua j e f = f / j , Π-extension-is-extension ua j e f

universes-are-injective-Π' : is-univalent 𝓤 → injective-type (𝓤 ̇) 𝓤 𝓤
universes-are-injective-Π' = universes-are-injective-Π

universes-are-injective-Σ : is-univalent (𝓤 ⊔ 𝓥) → injective-type (𝓤 ⊔ 𝓥 ̇) 𝓤 𝓥
universes-are-injective-Σ ua j e f = f ∖ j , λ x → eqtoid ua _ _ (Σ-extension-in-range f j e x)

retract-Of-injective : (D' : 𝓦' ̇) (D : 𝓦 ̇)
                     → injective-type D 𝓤 𝓥
                     → retract D' Of D
                     → injective-type D' 𝓤 𝓥
retract-Of-injective D' D i (r , ρ) {X} {Y} j e f = r ∘ g , γ
  where
    s : D' → D
    s d' = pr₁ (ρ d')
    rs : r ∘ s ∼ id
    rs d' = pr₂(ρ d')
    g : Y → D
    g = pr₁(i j e (s ∘ f))
    h : g ∘ j ∼ s ∘ f
    h = pr₂(i j e (s ∘ f))
    γ : r ∘ g ∘ j ∼ f
    γ x = ap r (h x) ∙ rs (f x)

injective-is-retract-of-power-of-universe : (D : 𝓤 ̇) → is-univalent 𝓤
                                          → injective-type D 𝓤  (𝓤 ⁺)
                                          → retract D Of (D → 𝓤 ̇)
injective-is-retract-of-power-of-universe D ua i = pr₁ a , λ y → (Id y , pr₂ a y)
  where
    a : Σ \r  → r ∘ Id ∼ id
    a = i Id (UA-Id-embedding ua fe) id

product-of-injective : {A : 𝓣 ̇} {D : A → 𝓦 ̇}
                     → ((a : A) → injective-type (D a) 𝓤 𝓥)
                     → injective-type (Π D) 𝓤 𝓥
product-of-injective {𝓣}  {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = f' , g
  where
    l : (a : A) → Σ \(h : Y → D a) → h ∘ j ∼ (λ x → f x a)
    l a = (i a) j e (λ x → f x a)

    f' : Y → (a : A) → D a
    f' y a = pr₁ (l a) y

    g : f' ∘ j ∼ f
    g x = dfunext (fe 𝓣 𝓦) (λ a → pr₂ (l a) x)

power-of-injective : {A : 𝓣 ̇} {D : 𝓦 ̇}
                   → injective-type D 𝓤 𝓥
                   → injective-type (A → D) 𝓤 𝓥
power-of-injective i = product-of-injective (λ a → i)

\end{code}

The following is the first of a number of injectivity resizing
constructions:

\begin{code}

injective-resizing₀ : is-univalent 𝓤
                    → (D : 𝓤 ̇) → injective-type D 𝓤 (𝓤 ⁺) → injective-type D 𝓤 𝓤
injective-resizing₀ {𝓤} ua D i = φ (injective-is-retract-of-power-of-universe D ua i)
 where
  φ : retract D Of (D → 𝓤 ̇) → injective-type D 𝓤 𝓤
  φ = retract-Of-injective D (D → 𝓤 ̇) (power-of-injective (universes-are-injective-Π ua))

\end{code}

Propositional resizing gives a much more general injectivity resizing
(see below).

Added 18th July 2018. Notice that the function e : X → Y doesn't need
to be an embedding and that the proof is completely routine.

\begin{code}

retract-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} (A : X → 𝓦 ̇) (B : X → 𝓣 ̇) (e : X → Y)
                  → ((x : X) → retract (A x) of (B x))
                  → ((y : Y) → retract ((A / e) y) of ((B / e) y))
retract-extension {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} A B e ρ y = r , s , rs
 where
  R : (x : X) → B x → A x
  R x = retraction (ρ x)
  S : (x : X) → A x → B x
  S x = section (ρ x)
  RS : (x : X) (a : A x) → R x (S x a) ≡ a
  RS x = retract-condition (ρ x)
  r : (B / e) y → (A / e) y
  r v (x , p) = R x (v (x , p))
  s : (A / e) y → (B / e) y
  s u (x , p) = S x (u (x , p))
  h : (u : (A / e) y) (σ : fiber e y) → r (s u) σ ≡ u σ
  h u (x , p) = RS x (u (x , p))
  rs : (u : (A / e) y) → r (s u) ≡ u
  rs u = dfunext (fe (𝓤 ⊔ 𝓥) 𝓦) (h u)

\end{code}

Added 25th July 2018.

\begin{code}

iterated-extension : {X : 𝓤 ̇} {Y : 𝓥 ̇} {Z : 𝓦 ̇} {A : X → 𝓣 ̇}
                     (j : X → Y) (k : Y → Z)
                   → (z : Z) → ((A / j) / k) z ≃ (A / (k ∘ j)) z
iterated-extension {𝓤} {𝓥} {𝓦} {𝓣} {X} {Y} {Z} {A} j k z = γ
 where
  f : ((A / j) / k) z → (A / (k ∘ j)) z
  f u (x , p) = u (j x , p) (x , refl)
  g : (A / (k ∘ j)) z → ((A / j) / k) z
  g v (.(j x) , q) (x , refl) = v (x , q)
  fg : (v : (A / (k ∘ j)) z) → f (g v) ≡ v
  fg v = refl
  gf' : (u : ((A / j) / k) z) (w : fiber k z) (t : fiber j (pr₁ w))
      → g (f u) w t ≡ u w t
  gf' u (.(j x) , q) (x , refl) = refl
  gf : (u : ((A / j) / k) z) → g (f u) ≡ u
  gf u = dfunext (fe (𝓥 ⊔ 𝓦) (𝓤 ⊔ 𝓥 ⊔ 𝓣))
          (λ w → dfunext (fe (𝓤 ⊔ 𝓥) 𝓣) (gf' u w))
  γ : ((A / j) / k) z ≃ (A / (k ∘ j)) z
  γ = f , ((g , fg) , (g , gf))

\end{code}

Added 9th November 2018.

We want to show that f ↦ f/j is an embedding of (X → 𝓤) into (Y → 𝓤)
if j is an embedding.

                   j
              X ------> Y
               \       /
                \     /
             f   \   / f/j
                  \ /
                   v
                   𝓤

The simplest case is X = P and Y = 𝟙, where P is a proposition. Then
the map P → 𝟙 is an embedding.

                   j
              P ------> 𝟙
               \       /
                \     /
              f  \   / (f / j) (x) = Π (w : fiber j x) → f(pr₁ w)
                  \ /              ≃ Π (p : P) → j p ≡ x → f p
                   v               ≃ Π (p : P) → f p
                   𝓤

So in essence we are considering the map s : (P → 𝓤) → 𝓤 defined by

   s f = Π (p : P) → f p.

Then, for any X : 𝓤,

  fiber s X = Σ \(f : P → 𝓤) → (Π (p : P) → f p) ≡ X.

A few days pause. Now 15th Nov 2018 after a discussion in the HoTT list.
https://groups.google.com/d/topic/homotopytypetheory/xvx5hOEPnDs/discussion

Here is my take on the outcome of the discussion, following
independent solutions by Shulman and Capriotti.

\begin{code}

module /-extension-is-embedding-special-case
         (P : 𝓤 ̇)
         (i : is-prop P)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-Equiv-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = funext-from-univalence ua

 r :  𝓤 ̇ → (P → 𝓤 ̇)
 r X p = X

 s : (P → 𝓤 ̇) → 𝓤 ̇
 s = Π

 rs : ∀ A → r (s A) ≡ A
 rs A = dfunext fe' (λ p → eqtoid ua (s A) (A p) (prop-indexed-product feuu i p))

 sr : ∀ X → s (r X) ≡ (P → X)
 sr X = refl

 κ : (X : 𝓤 ̇) → X → s (r X)
 κ X x p = x

 M : 𝓤 ⁺ ̇
 M = Σ \(X : 𝓤 ̇) → is-equiv (κ X)

 φ : (P → 𝓤 ̇) → M
 φ A = s A , qinvs-are-equivs (κ (s A)) (δ , ε , η)
  where
   δ : (P → s A) → s A
   δ v p = v p p
   η : (v : P → s A) → κ (s A) (δ v) ≡ v
   η v = dfunext feuu (λ p → dfunext feuu (λ q → ap (λ - → v - q) (i q p)))
   ε : (u : Π A) → δ (κ (s A) u) ≡ u
   ε u = refl

 γ : M → (P → 𝓤 ̇)
 γ (X , i) = r X

 φγ : (m : M) → φ (γ m) ≡ m
 φγ (X , i) = to-Σ-≡ (eqtoid ua (P → X) X (≃-sym (κ X , i)) ,
                      being-equiv-is-a-prop fe (κ X) _ i)

 γφ : (A : P → 𝓤 ̇) → γ (φ A) ≡ A
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → 𝓤 ̇
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-embedding (λ X → being-equiv-is-a-prop fe (κ X))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

Also 15th Nov 2018. We have a dual situation:

\begin{code}

module ∖-extension-is-embedding-special-case
         (P : 𝓤 ̇)
         (i : is-prop P)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt

 s : (P → 𝓤 ̇) → 𝓤 ̇
 s = Σ

 r :  𝓤 ̇ → (P → 𝓤 ̇)
 r X p = X

 rs : ∀ A → r (s A) ≡ A
 rs A = dfunext fe' (λ p → eqtoid ua (Σ A) (A p) (prop-indexed-sum i p))

 sr : ∀ X → s (r X) ≡ P × X
 sr X = refl

 κ : (X : 𝓤 ̇) → s (r X) → X
 κ X = pr₂

 C : 𝓤 ⁺ ̇
 C = Σ \(X : 𝓤 ̇) → is-equiv (κ X)

 φ : (P → 𝓤 ̇) → C
 φ A = s A , qinvs-are-equivs (κ (s A)) (δ , ε , η)
  where
   δ : s A → P × s A
   δ (p , a) = p , p , a
   η : (σ : s A) → κ (s A) (δ σ) ≡ σ
   η σ = refl
   ε : (τ : P × s A) → δ (κ (s A) τ) ≡ τ
   ε (p , q , a) = to-×-≡ (i q p) refl

 γ : C → (P → 𝓤 ̇)
 γ (X , i) = r X

 φγ : (c : C) → φ (γ c) ≡ c
 φγ (X , i) = to-Σ-≡ (eqtoid ua (P × X) X (κ X , i) ,
                     (being-equiv-is-a-prop fe (κ X) _ i))

 γφ : (A : P → 𝓤 ̇) → γ (φ A) ≡ A
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : C → 𝓤 ̇
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-embedding (λ X → being-equiv-is-a-prop fe (κ X))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 20th November 2018.

\begin{code}

module /-extension-is-embedding
         (X Y : 𝓤 ̇)
         (j : X → Y)
         (i : is-embedding j)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt
 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = funext-from-univalence ua

 s : (X → 𝓤 ̇) → (Y → 𝓤 ̇)
 s f = f / j

 r : (Y → 𝓤 ̇) → (X → 𝓤 ̇)
 r g = g ∘ j

 rs : ∀ f → r (s f) ≡ f
 rs = Π-extension-is-extension' ua fe' j i

 sr : ∀ g → s (r g) ≡ (g ∘ j) / j
 sr g = refl

 κ : (g : Y → 𝓤 ̇) → g ≾ s (r g)
 κ g y C (x , p) = back-transport g p C

 M : (𝓤 ⁺) ̇
 M = Σ \(g : Y → 𝓤 ̇) → (y : Y) → is-equiv (κ g y)

 φ : (X → 𝓤 ̇) → M
 φ f = s f , e
  where
   e : (y : Y) → is-equiv (κ (s f) y)
   e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
    where
     δ : (((f / j) ∘ j) / j) y → (f / j) y
     δ C (x , p) = C (x , p) (x , refl)
     η : (C : ((f / j ∘ j) / j) y) → κ (s f) y (δ C) ≡ C
     η C = dfunext feuu g
      where
       g : (w : fiber j y) → κ (s f) y (δ C) w ≡ C w
       g (x , refl) = dfunext feuu h
        where
         h : (t : fiber j (j x)) → C t (pr₁ t , refl) ≡ C (x , refl) t
         h (x' , p') = transport (λ - → C - (pr₁ - , refl) ≡ C (x , refl) -) q refl
          where
           q : (x , refl) ≡ (x' , p')
           q = i (j x) (x , refl) (x' , p')
     ε : (a : (f / j) y) → δ (κ (s f) y a) ≡ a
     ε a = dfunext feuu g
      where
       g : (w : fiber j y) → δ (κ (s f) y a) w ≡ a w
       g (x , refl) = refl

 γ : M → (X → 𝓤 ̇)
 γ (g , e) = r g

 φγ : ∀ m → φ (γ m) ≡ m
 φγ (g , e) = to-Σ-≡
               (dfunext fe' (λ y → eqtoid ua (s (r g) y) (g y) (≃-sym (κ g y , e y))) ,
                Π-is-prop feuu (λ y → being-equiv-is-a-prop'' feuu (κ g y)) _ e)

 γφ : ∀ f → γ (φ f) ≡ f
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → (Y → 𝓤 ̇)
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-embedding (λ g → Π-is-prop feuu (λ y → being-equiv-is-a-prop'' feuu (κ g y)))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 21th November 2018.

\begin{code}

module ∖-extension-is-embedding
         (X Y : 𝓤 ̇)
         (j : X → Y)
         (ej : is-embedding j)
         (fe' : funext 𝓤 (𝓤 ⁺))
         (ua : is-univalent 𝓤)
       where

 open import UF-PropIndexedPiSigma
 open import UF-Equiv-FunExt
 open import UF-Subsingletons-FunExt
 open import UF-UA-FunExt

 feuu : funext 𝓤 𝓤
 feuu = funext-from-univalence ua

 s : (X → 𝓤 ̇) → (Y → 𝓤 ̇)
 s f = f ∖ j

 r : (Y → 𝓤 ̇) → (X → 𝓤 ̇)
 r g = g ∘ j

 rs : ∀ f → r (s f) ≡ f
 rs = Σ-extension-is-extension' ua fe' j ej

 sr : ∀ g → s (r g) ≡ (g ∘ j) ∖ j
 sr g = refl

 κ : (g : Y → 𝓤 ̇) → s (r g) ≾ g
 κ g y ((x , p) , C) = transport g p C

 M : (𝓤 ⁺) ̇
 M = Σ \(g : Y → 𝓤 ̇) → (y : Y) → is-equiv (κ g y)
 φ : (X → 𝓤 ̇) → M
 φ f = s f , e
  where
   e : (y : Y) → is-equiv (κ (s f) y)
   e y = qinvs-are-equivs (κ (s f) y) (δ , ε , η)
    where
     δ : (Σ \(w : fiber j y) → f(pr₁ w))
       → Σ \(t : fiber j y) → Σ (\(w : fiber j (j (pr₁ t))) → f (pr₁ w))
     δ ((x , p) , C) = (x , p) , (x , refl) , C
     η : (σ : s f y) → κ (s f) y (δ σ) ≡ σ
     η ((x , refl) , C) = refl
     ε : (τ : Σ (λ w → r (s f) (pr₁ w))) → δ (κ (s f) y τ) ≡ τ
     ε ((x , refl) , (x' , p') , C) = t x x' (pa x' x p') p' C (appa x x' p')
      where
        t : (x x' : X) (u : x' ≡ x) (p : j x' ≡ j x) (C : f x') → (ap j u ≡ p) →
            ((x' , p)    , (x' , refl) , C)
         ≡ (((x  , refl) , (x' , p)    , C) ∶ Σ \w → r (s f) (pr₁ w))
        t x .x refl p C refl = refl
        ej' : ∀ x x' → qinv (ap j {x} {x'})
        ej' x x' = equivs-are-qinvs (ap j) (embedding-embedding' j ej x x')
        pa : ∀ x x' → j x ≡ j x' → x ≡ x'
        pa x x' = pr₁ (ej' x x')
        appa : ∀ x x' p' → ap j (pa x' x p') ≡ p'
        appa x x' = pr₂ (pr₂ (ej' x' x))

 γ : M → (X → 𝓤 ̇)
 γ (g , e) = r g

 φγ : ∀ m → φ (γ m) ≡ m
 φγ (g , e) = to-Σ-≡
               (dfunext fe' (λ y → eqtoid ua (s (r g) y) (g y) (κ g y , e y)) ,
                Π-is-prop feuu (λ y → being-equiv-is-a-prop'' feuu (κ g y)) _ e)

 γφ : ∀ f → γ (φ f) ≡ f
 γφ = rs

 φ-is-equiv : is-equiv φ
 φ-is-equiv = qinvs-are-equivs φ (γ , γφ , φγ)

 φ-is-embedding : is-embedding φ
 φ-is-embedding = equivs-are-embeddings φ φ-is-equiv

 ψ : M → (Y → 𝓤 ̇)
 ψ = pr₁

 ψ-is-embedding : is-embedding ψ
 ψ-is-embedding = pr₁-embedding (λ g → Π-is-prop feuu (λ y → being-equiv-is-a-prop'' feuu (κ g y)))

 s-is-comp : s ≡ ψ ∘ φ
 s-is-comp = refl

 s-is-embedding : is-embedding s
 s-is-embedding = comp-embedding φ-is-embedding ψ-is-embedding

\end{code}

Added 23rd Nov 2018, version of 21st January 2017:

NB. The notion of flabbiness used in topos theory is defined with truncated Σ.

\begin{code}

flabby : 𝓦 ̇ → (𝓤 : Universe) → 𝓦 ⊔ 𝓤 ⁺ ̇
flabby D 𝓤 = (P : 𝓤 ̇) → is-prop P → (f : P → D) → Σ \(d : D) → (p : P) → d ≡ f p

flabby-pointed : (D : 𝓦 ̇) → flabby D 𝓤 → D
flabby-pointed D φ = pr₁ (φ 𝟘 𝟘-is-prop unique-from-𝟘)


injective-types-are-flabby : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → flabby D 𝓤
injective-types-are-flabby {𝓦} {𝓤} {𝓥} D i P isp f = pr₁ (i (λ p → *) (prop-embedding P isp 𝓥) f) * ,
                                                      pr₂ (i (λ p → *) (prop-embedding P isp 𝓥) f)

flabby-types-are-injective : (D : 𝓦 ̇) → flabby D (𝓤 ⊔ 𝓥) → injective-type D 𝓤 𝓥
flabby-types-are-injective D φ {X} {Y} j e f = f' , p
 where
  f' : Y → D
  f' y = pr₁ (φ (fiber j y) (e y) (f ∘ pr₁))
  p : (x : X) → f' (j x) ≡ f x
  p x = q (x , refl)
   where
    q : (w : fiber j (j x)) → f' (j x) ≡ f (pr₁ w)
    q = pr₂ (φ (fiber j (j x)) (e (j x)) (f ∘ pr₁))

\end{code}

Because Ω is a retract of 𝓤 via propositional truncation, it is
injective. But we can prove this directly without assumming
propositional truncations, and propositional and functional
extensionality (which give to propositional univalence) are enough,
whereas the injectivity of the universe requires full univalence.

\begin{code}

Ω-flabby : {𝓤 𝓥 : Universe} → propext (𝓤 ⊔ 𝓥) → flabby (Ω (𝓤 ⊔ 𝓥)) 𝓤
Ω-flabby {𝓤} {𝓥} pe P i f = (Q , j) , c
 where
  Q : 𝓤 ⊔ 𝓥 ̇
  Q = (p : P) → f p holds
  j : is-prop Q
  j = Π-is-prop (fe 𝓤 (𝓤 ⊔ 𝓥)) (λ p → holds-is-prop (f p))
  c : (p : P) → Q , j ≡ f p
  c p = to-Σ-≡ (t , being-a-prop-is-a-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥)) _ _)
   where
      g : Q → f p holds
      g q = q p
      h : f p holds → Q
      h r p' = transport (λ - → f - holds) (i p p') r
      t : Q ≡ f p holds
      t = pe j (holds-is-prop (f p)) g h

Ω-injective : {𝓤 𝓥 : Universe} → propext (𝓤 ⊔ 𝓥) → injective-type (Ω (𝓤 ⊔ 𝓥)) 𝓤 𝓥
Ω-injective {𝓤} {𝓥} pe = flabby-types-are-injective (Ω (𝓤 ⊔ 𝓥)) (Ω-flabby {𝓤 ⊔ 𝓥} {𝓤} pe)

\end{code}

Added 6th Feb 2019.

The injectivity of all types is logically equivalent to excluded middle
(even though excluded middle is a proposition but injectivity is data):

\begin{code}

EM-gives-pointed-types-flabby : (D : 𝓦 ̇) → EM 𝓤 → D → flabby D 𝓤
EM-gives-pointed-types-flabby {𝓦} {𝓤} D em d P i f = h (em P i)
 where
  h : P + ¬ P → Σ \(d : D) → (p : P) → d ≡ f p
  h (inl p) = f p , (λ q → ap f (i p q))
  h (inr n) = d , (λ p → 𝟘-elim (n p))

pointed-types-flabby-gives-EM : ((D : 𝓦 ̇) → D → flabby D 𝓦) → EM 𝓦
pointed-types-flabby-gives-EM {𝓦} α P i = γ
 where
  D = (P + ¬ P) + 𝟙 {𝓦}
  f : P + ¬ P → D
  f (inl p) = inl (inl p)
  f (inr n) = inl (inr n)
  d : D
  d = pr₁ (α D (inr *) (P + ¬ P) (decidable-types-are-props (fe 𝓦 𝓤₀) i) f)
  φ : (z : P + ¬ P) → d ≡ f z
  φ = pr₂ (α D (inr *) (P + ¬ P) (decidable-types-are-props (fe 𝓦 𝓤₀) i) f)
  a : (p : P) → d ≡ inl (inl p)
  a p = φ (inl p)
  b : (n : ¬ P) → d ≡ inl (inr n)
  b n = φ (inr n)
  δ : (d' : D) → d ≡ d' → P + ¬ P
  δ (inl (inl p)) r = inl p
  δ (inl (inr n)) r = inr n
  δ (inr *)       r = 𝟘-elim (m n)
   where
    n : ¬ P
    n p = 𝟘-elim (+disjoint ((a p)⁻¹ ∙ r))
    m : ¬¬ P
    m n = 𝟘-elim (+disjoint ((b n)⁻¹ ∙ r))
  γ : P + ¬ P
  γ = δ d refl

EM-gives-pointed-types-injective : (D : 𝓦 ̇) → EM (𝓤 ⊔ 𝓥) → D → injective-type D 𝓤 𝓥
EM-gives-pointed-types-injective D em d = flabby-types-are-injective D (EM-gives-pointed-types-flabby D em d)

pointed-types-injective-gives-EM : ((D : 𝓦 ̇) → D → injective-type D 𝓦 𝓤) → EM 𝓦
pointed-types-injective-gives-EM α = pointed-types-flabby-gives-EM (λ D d → injective-types-are-flabby D (α D d))

\end{code}

End of 6th Feb addition. But this is not the end of the story. What
happens with anonymous injectivity (defined and studied below)?

TODO. Show that the extension induced by flabbiness is an embedding of
function types.

Without resizing axioms, we have the following resizing construction:

\begin{code}

injective-resizing₁ : (D : 𝓦 ̇) → injective-type D (𝓤 ⊔ 𝓣) 𝓥 → injective-type D 𝓤 𝓣
injective-resizing₁ D i j e f = flabby-types-are-injective D (injective-types-are-flabby D i) j e f

\end{code}

In particular:

\begin{code}

injective-resizing₂ : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤 𝓤
injective-resizing₂ = injective-resizing₁

injective-resizing₃ : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤₀ 𝓤
injective-resizing₃ = injective-resizing₁

\end{code}

Added 24th January 2019.

With propositional resizing, as soon as D is flabby with respect to
some universe, it is flabby with respect to all universes:

\begin{code}

flabiness-resizing : (D : 𝓦 ̇) (𝓤 𝓥 : Universe) → propositional-resizing 𝓤 𝓥
                   → flabby D 𝓥 → flabby D 𝓤
flabiness-resizing D 𝓤 𝓥 R φ P i f = d , h
 where
  Q : 𝓥 ̇
  Q = resize R P i
  j : is-prop Q
  j = resize-is-a-prop R P i
  α : P → Q
  α = to-resize R P i
  β : Q → P
  β = from-resize R P i
  d : D
  d = pr₁ (φ Q j (f ∘ β))
  k : (q : Q) → d ≡ f (β q)
  k = pr₂ (φ Q j (f ∘ β))
  h : (p : P) → d ≡ f p
  h p = d           ≡⟨ k (α p) ⟩
        f (β (α p)) ≡⟨ ap f (i (β (α p)) p) ⟩
        f p         ∎

\end{code}

And from this it follows that the injectivity of a type with respect
to two given universes implies its injectivity with respect to all
universes:

\begin{code}

injective-resizing : ∀ {𝓤 𝓥 𝓤' 𝓥' 𝓦} → propositional-resizing (𝓤' ⊔ 𝓥') 𝓤
                   → (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → injective-type D 𝓤' 𝓥'
injective-resizing {𝓤} {𝓥} {𝓤'} {𝓥'} {𝓦} R D i j e f = flabby-types-are-injective D
                                                          (flabiness-resizing D (𝓤' ⊔ 𝓥') 𝓤 R
                                                            (injective-types-are-flabby D i)) j e f

\end{code}

As an application of this and of injectivity of universes, we have
that any universe is a retract of any larger universe.

We remark that for types that are not sets, sections are not
automatically embeddings (Shulman 2015, https://arxiv.org/abs/1507.03634).

\begin{code}

universe-retract : Univalence → Propositional-resizing
                 → (𝓤 𝓥 : Universe)
                 → Σ \(ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)) → is-embedding (section ρ)
universe-retract ua R 𝓤 𝓥 = ρ , (lift-is-embedding ua)
 where
  a : injective-type (𝓤 ̇) 𝓤 𝓤
  a = universes-are-injective-Π {𝓤} {𝓤} (ua 𝓤)
  b : is-embedding (lift 𝓥)
    → injective-type (𝓤 ̇) (𝓤 ⁺) ((𝓤 ⊔ 𝓥 )⁺)
    → retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)
  b = embedding-retract (𝓤 ̇) (𝓤 ⊔ 𝓥 ̇) (lift 𝓥)
  ρ : retract 𝓤 ̇ of (𝓤 ⊔ 𝓥 ̇)
  ρ = b (lift-is-embedding ua) (injective-resizing R (𝓤 ̇) a)

\end{code}

And unfolding of the above construction is in the module UF-Resizing.

Added 25th January 2019. From this we get the following
characterization of injective types (as a logical equivalence, not a
type equivalence), which can be read as saying that the injective
types in a universe 𝓤 are precisely the retracts of exponential powers
of 𝓤.

\begin{code}

injective-characterization : is-univalent 𝓤 → propositional-resizing (𝓤 ⁺) 𝓤 → (D : 𝓤 ̇)
                           → injective-type D 𝓤 𝓤 ⇔ Σ \(X : 𝓤 ̇) → retract D Of (X → 𝓤 ̇)
injective-characterization {𝓤} ua R D = a , b
 where
  a : injective-type D 𝓤 𝓤 → Σ \(X : 𝓤 ̇) → retract D Of (X → 𝓤 ̇)
  a i = D , d
   where
    c : injective-type D 𝓤 (𝓤 ⁺)
    c = injective-resizing R D i
    d : retract D Of (D → 𝓤 ̇)
    d = injective-is-retract-of-power-of-universe D ua c

  b : (Σ \(X : 𝓤 ̇) → retract D Of (X → 𝓤 ̇)) → injective-type D 𝓤 𝓤
  b (X , r) = d
   where
    c : injective-type (X → 𝓤 ̇) 𝓤 𝓤
    c = power-of-injective (universes-are-injective-Σ ua)
    d : injective-type D 𝓤 𝓤
    d = retract-Of-injective D (X → 𝓤 ̇) c r

\end{code}

Added 23rd January 2019:

\begin{code}

module injectivity-of-lifting (𝓤 : Universe) where

 open import Lifting 𝓤
 open import LiftingAlgebras 𝓤
 open import LiftingEmbeddingViaSIP 𝓤

 open import UF-UA-FunExt

\end{code}

The underlying types of algebras of the lifting monad are flabby, and
hence injective, and so in particular the underlying objects of the
free 𝓛-algebras are injective.

\begin{code}

 𝓛-alg-flabby : propext 𝓤 → funext 𝓤 𝓤 → funext 𝓤 𝓥
              → {A : 𝓥 ̇} → 𝓛-alg A → flabby A 𝓤
 𝓛-alg-flabby pe fe fe' (∐ , κ , ι) P i f = ∐ i f , γ
  where
   γ : (p : P) → ∐ i f ≡ f p
   γ p = 𝓛-alg-Law₀-gives₀' pe fe fe' ∐ κ P i f p

 𝓛-alg-injective : propext 𝓤 → funext 𝓤 𝓤 → funext 𝓤 𝓥
                 → (A : 𝓥 ̇) → 𝓛-alg A → injective-type A 𝓤 𝓤
 𝓛-alg-injective pe fe fe' A α = flabby-types-are-injective A (𝓛-alg-flabby pe fe fe' α)

 free-𝓛-algebra-injective : is-univalent 𝓤 → funext 𝓤 (𝓤 ⁺)
                          → (X : 𝓤 ̇) → injective-type (𝓛 X) 𝓤 𝓤
 free-𝓛-algebra-injective ua fe X = 𝓛-alg-injective
                                       (propext-from-univalence ua)
                                       (funext-from-univalence ua)
                                       fe
                                       (𝓛 X)
                                       (𝓛-algebra-gives-alg (free-𝓛-algebra ua X))
\end{code}

Because the unit of the lifting monad is an embedding, it follows that
injective types are retracts of underlying objects of free algebras:

\begin{code}

 injective-is-retract-of-free-𝓛-algebra : (D : 𝓤 ̇) → is-univalent 𝓤
                                        → injective-type D 𝓤 (𝓤 ⁺) → retract D Of (𝓛 D)
 injective-is-retract-of-free-𝓛-algebra D ua i = pr₁ a , λ γ → (η γ , pr₂ a γ)
   where
     a : Σ \r  → r ∘ η ∼ id
     a = i η (η-is-embedding' 𝓤 D ua (funext-from-univalence ua)) id

\end{code}

With propositional resizing, the injective types are precisely the
retracts of the underlying objects of free algebras of the lifting
monad:

\begin{code}

 injectives-in-terms-of-free-𝓛-algebras : is-univalent 𝓤 → funext 𝓤 (𝓤 ⁺) → propositional-resizing (𝓤 ⁺) 𝓤
                                        → (D : 𝓤 ̇) → injective-type D 𝓤 𝓤 ⇔ Σ \(X : 𝓤 ̇) → retract D Of (𝓛 X)
 injectives-in-terms-of-free-𝓛-algebras ua fe R D = a , b
  where
   a : injective-type D 𝓤 𝓤 → Σ \(X : 𝓤 ̇) → retract D Of (𝓛 X)
   a i = D , injective-is-retract-of-free-𝓛-algebra D ua (injective-resizing R D i)
   b : (Σ \(X : 𝓤 ̇) → retract D Of (𝓛 X)) → injective-type D 𝓤 𝓤
   b (X , r) = retract-Of-injective D (𝓛 X) (free-𝓛-algebra-injective ua fe X) r

\end{code}

Added 21st January 2019. We now consider injectivity as property
rather than data.

\begin{code}

module anonymously-injective (pt : propositional-truncations-exist) where

 open PropositionalTruncation pt

 ainjective-type : 𝓦 ̇ → (𝓤 𝓥 : Universe) → 𝓤 ⁺ ⊔ 𝓥  ⁺ ⊔ 𝓦 ̇
 ainjective-type D 𝓤 𝓥 = {X : 𝓤 ̇} {Y : 𝓥 ̇} (j : X → Y) → is-embedding j
                       → (f : X → D) → ∃ \(f' : Y → D) → f' ∘ j ∼ f


 ainjectivity-is-a-prop : (D : 𝓦 ̇) (𝓤 𝓥 : Universe)
                        → is-prop (ainjective-type D 𝓤 𝓥)
 ainjectivity-is-a-prop {𝓦} D 𝓤 𝓥 = Π-is-prop' (fe (𝓤 ⁺) (𝓤 ⊔ (𝓥 ⁺) ⊔ 𝓦))
                                        (λ X → Π-is-prop' (fe (𝓥 ⁺) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                          (λ Y → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                            (λ j → Π-is-prop (fe (𝓤 ⊔ 𝓥) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                              (λ e → Π-is-prop (fe (𝓤 ⊔ 𝓦) (𝓤 ⊔ 𝓥 ⊔ 𝓦))
                                                (λ f → ∥∥-is-a-prop)))))


 injective-gives-ainjective : (D : 𝓦 ̇) → injective-type D 𝓤 𝓥 → ainjective-type D 𝓤 𝓥
 injective-gives-ainjective D i j e f = ∣ i j e f ∣

 ∥injective∥-gives-ainjective : (D : 𝓦 ̇) → ∥ injective-type D 𝓤 𝓥 ∥ → ainjective-type D 𝓤 𝓥
 ∥injective∥-gives-ainjective {𝓦} {𝓤} {𝓥} D = ∥∥-rec (ainjectivity-is-a-prop D 𝓤 𝓥)
                                                     (injective-gives-ainjective D)

 retract-of-ainjective : (D' : 𝓤 ̇) (D : 𝓥 ̇)
                       → ainjective-type D 𝓦 𝓣
                       → retract D' of D
                       → ainjective-type D' 𝓦 𝓣
 retract-of-ainjective D' D i (r , (s , rs)) {X} {Y} j e f = γ
  where
   i' : ∃ \(f' : Y → D) → f' ∘ j ∼ s ∘ f
   i' = i j e (s ∘ f)
   φ : (Σ \(f' : Y → D) → f' ∘ j ∼ s ∘ f) → Σ \(f'' : Y → D') → f'' ∘ j ∼ f
   φ (f' , h) = r ∘ f' , (λ x → ap r (h x) ∙ rs (f x))
   γ : ∃ \(f'' : Y → D') → f'' ∘ j ∼ f
   γ = ∥∥-functor φ i'

 retract-Of-ainjective : (D' : 𝓤 ̇) (D : 𝓥 ̇)
                       → ainjective-type D 𝓦 𝓣
                       → ∥ retract D' Of D ∥
                       → ainjective-type D' 𝓦 𝓣
 retract-Of-ainjective {𝓤} {𝓥} {𝓦} {𝓣} D' D i =
   ∥∥-rec (ainjectivity-is-a-prop D' 𝓦 𝓣)
          (retract-of-ainjective D' D i ∘ retract-Of-retract-of)

\end{code}

The give proof of power-of-injective doesn't adapt to the following,
so we need a new proof, but also new universe assumptions.

\begin{code}

 power-of-ainjective : {A : 𝓣 ̇} {D : 𝓣 ⊔ 𝓦 ̇}
                     → ainjective-type D       (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
                     → ainjective-type (A → D) (𝓤 ⊔ 𝓣) (𝓥 ⊔ 𝓣)
 power-of-ainjective {𝓣}  {𝓦} {𝓤} {𝓥} {A} {D} i {X} {Y} j e f = γ
  where
   g : X × A → D
   g = uncurry f
   k : X × A → Y × A
   k (x , a) = j x , a
   c : is-embedding k
   c = pair-fun-embedding j (λ x a → a) e (λ x → id-is-embedding)
   ψ : ∃ \(g' : Y × A → D) → g' ∘ k ∼ g
   ψ = i k c g
   φ : (Σ \(g' : Y × A → D) → g' ∘ k ∼ g) → (Σ \(f' : Y → (A → D)) → f' ∘ j ∼ f)
   φ (g' , h) = curry g' , (λ x → dfunext (fe 𝓣 (𝓣 ⊔ 𝓦)) (λ a → h (x , a)))
   γ : ∃ \(f' : Y → (A → D)) → f' ∘ j ∼ f
   γ = ∥∥-functor φ ψ

 ainjective-retract-of-power-of-universe : (D : 𝓤 ̇) → is-univalent 𝓤
                                         → ainjective-type D 𝓤 (𝓤 ⁺)
                                         → ∥ retract D Of (D → 𝓤 ̇) ∥
 ainjective-retract-of-power-of-universe D ua i = ∥∥-functor retract-of-retract-Of γ
  where
    a : ∃ \r  → r ∘ Id ∼ id
    a = i Id (UA-Id-embedding ua fe) id
    φ : (Σ \r  → r ∘ Id ∼ id) → Σ \r  → Σ \s → r ∘ s ∼ id
    φ (r , p) = r , Id , p
    γ : ∃ \r  → Σ \s → r ∘ s ∼ id
    γ = ∥∥-functor φ a

 ainjective-gives-∥injective∥ : is-univalent 𝓤
                             → (D : 𝓤 ̇)
                             → ainjective-type D 𝓤 (𝓤 ⁺)
                             → ∥ injective-type D 𝓤 𝓤 ∥
 ainjective-gives-∥injective∥ {𝓤} ua D i = γ
  where
   φ : retract D Of (D → 𝓤 ̇) → injective-type D 𝓤 𝓤
   φ = retract-Of-injective D (D → 𝓤 ̇) (power-of-injective (universes-are-injective-Π ua))
   γ : ∥ injective-type D 𝓤 𝓤 ∥
   γ = ∥∥-functor φ (ainjective-retract-of-power-of-universe D ua i)

\end{code}

So, in summary, regarding the relationship between ainjectivity and
truncated injectivity, so far we know that

  ∥ injective-type D 𝓤 𝓥 ∥ → ainjective-type D 𝓤 𝓥

and

  ainjective-type D 𝓤 (𝓤 ⁺) → ∥ injective-type D 𝓤 𝓤 ∥,

and hence, using propositional resizing, we get the following
characterization of a particular case of ainjectivity in terms of
injectivity.

\begin{code}

 ainjectivity-in-terms-of-injectivity : is-univalent 𝓤
                                      → propositional-resizing (𝓤 ⁺) 𝓤
                                      → (D : 𝓤  ̇) → ainjective-type D 𝓤 (𝓤 ⁺)
                                                   ⇔ ∥ injective-type D 𝓤 (𝓤 ⁺) ∥
 ainjectivity-in-terms-of-injectivity {𝓤} ua R D = a , b
  where
   a : ainjective-type D 𝓤 (𝓤 ⁺) → ∥ injective-type D 𝓤 (𝓤 ⁺) ∥
   a = ∥∥-functor (injective-resizing R D) ∘ ainjective-gives-∥injective∥ ua D
   b : ∥ injective-type D 𝓤 (𝓤 ⁺) ∥ → ainjective-type D 𝓤 (𝓤 ⁺)
   b = ∥injective∥-gives-ainjective D

\end{code}

What we really would like to have for D : 𝓤 is

  ainjective-type D 𝓤 𝓤 ⇔ ∥ injective-type D 𝓤 𝓤 ∥,

and, perhaps, more generally, also

  ainjective-type D 𝓥 𝓦 ⇔ ∥ injective-type D 𝓤 𝓦 ∥,

but this requires further thought. (It may be easy given the above
development. Or hard or impossible.)

TODO. I think that, with resizing, for a *set* D:𝓤 in universe 𝓤 other
than 𝓤₀ (that is, of the form 𝓥 ⁺) we do have

  ainjective-type D 𝓤 𝓤 ⇔ ∥ injective-type D 𝓤 𝓤 ∥,

The reason is that the embedding Id : D → (D → 𝓤) factors through (D →
Ω₀) because D is a set and propositional resizing holds.

Fixities:

\begin{code}

infixr 4 _≾_

\end{code}

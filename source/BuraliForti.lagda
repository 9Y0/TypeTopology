Martin Escardo, 21-25 December 2020.

The Burali-Forti argument in HoTT/UF
------------------------------------

Abstract. We use the Burali-Forti argument to show that, in HoTT/UF,
no universe embedding

    𝓤 → 𝓤⁺.

of a universe 𝓤 into its successor 𝓤⁺ is an equivalence, and neither
is any hSet embedding

    hSet 𝓤 → hSet 𝓤⁺

of the type of sets of 𝓤 into that of 𝓤⁺.

We work with ordinals as defined in the HoTT book.
https://homotopytypetheory.org/book/

Introduction
------------

Univalence is used three times (at least):

    1. to know that the type of ordinals is a 0-type and hence all
       ordinals form an ordinal in the next universe,

    2. to develop the Burali-Forti argument that no ordinal is
       equivalent to the ordinal of all ordinals,

    3. to resize down the values of the order relation of the ordinal
       of ordinals, to conclude that the ordinal of ordinals is large.

There are also a number of uses of univalence via functional and
propositional extensionality.

Propositional resizing is not needed, thanks to (3).

An ordinal in a universe 𝓤 is a type X : 𝓤 equipped with a relation

    _≺_ : X → X → 𝓤

required to be

    1. proposition-valued,

    2. transitive,

    3. extensional (any two points with same lower set are the same),

    4. well founded (every element is accessible, or, equivalently,
       the principle of transfinite induction holds).

The HoTT book additionally requires X to be a set, but this follows
automatically from the above requirements for the order.

We denote by

    Ordinal 𝓤

the type of ordinals in a universe 𝓤.

The underlying type of an ordinal α is denoted by ⟨ α ⟩ and its order
relation is denoted by _≺⟨ α ⟩_.

Equivalence of ordinals,

    _≃ₒ_ : Ordinal 𝓤 → Ordinal 𝓥 → 𝓤 ⊔ 𝓥,

means that that there is an equivalence of the underlying types that
preserves and reflects order.

For ordinals α and β in the *same* universe, their identity type α ≡ β
is canonically equivalent to the ordinal-equivalence type α ≃ₒ β,
by univalence.

The lower set of a point x : ⟨ α ⟩ is written α ↓ x, and is itself an
ordinal under the inherited order. The ordinals in a universe 𝓤 form
an ordinal in the successor universe 𝓤⁺, denoted by

    OrdinalOfOrdinals 𝓤 : Ordinal 𝓤⁺.

Its order relation is denoted by _⊲_ and is defined by

    α ⊲ β = Σ b ꞉ ⟨ β ⟩ , α ≡ (β ↓ b).

This order has type

    _⊲_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤⁺,

as required for it to make the type Ordinal 𝓤 into an ordinal in the
next universe, but it is pointwise equivalent to the "resized down"
order

    _⊲⁻_ : Ordinal 𝓤 → Ordinal 𝓤 → 𝓤

defined by

    α ⊲⁻ β = Σ b ꞉ ⟨ β ⟩ , α ≃₀ (β ↓ b).

The existence of such a resized-down order is crucial for the
corollaries of Burali-Forti, but not for Burali-Forti itself.

Agda formulation of the Burali-Forti argument and its corollaries
-----------------------------------------------------------------

\begin{code}

{-# OPTIONS --without-K --exact-split --safe #-}

\end{code}

As discussed above, we assume univalence as a hypothesis:

\begin{code}

open import UF-Univalence

module BuraliForti
       (ua : Univalence)
       where

open import SpartanMLTT
open import OrdinalNotions
open import OrdinalsType
open import OrdinalOfOrdinals ua
open import OrdinalsWellOrderTransport

open import UF-Base
open import UF-Subsingletons
open import UF-Retracts
open import UF-Equiv
open import UF-UniverseEmbedding

\end{code}

Our version of Burali-Forti says that there is no ordinal in the
universe 𝓤 equivalent to the ordinal of all ordinals in the universe 𝓤.

\begin{code}

Burali-Forti : ¬ (Σ α ꞉ Ordinal 𝓤 , α ≃ₒ OrdinalOfOrdinals 𝓤)
Burali-Forti {𝓤} (α , 𝕗) = γ
 where
  A : Ordinal (𝓤 ⁺)
  A = OrdinalOfOrdinals 𝓤

  a : A ≃ₒ α
  a = ≃ₒ-sym α A 𝕗

  b : α ≃ₒ (A ↓ α)
  b = ordinals-in-O-are-lowersets-of-O α

  c : A ≃ₒ (A ↓ α)
  c = ≃ₒ-trans A α (A ↓ α) a b

  d : A ≡ (A ↓ α)
  d = eqtoidₒ A (A ↓ α) c

  e : A ⊲ A
  e = α , d

  γ : 𝟘
  γ = accessible-points-are-irreflexive _⊲_ A (⊲-is-well-founded A) e

\end{code}

Side-remark. The following cleaner rendering of the above makes Agda
2.6.1 (and the development version 2.6.2 as of 25 December 2020) hang
when it reaches d in the definition of e':
\begin{code}
{-
  𝓐 : Ordinal (𝓤 ⁺ ⁺)
  𝓐 = OrdinalOfOrdinals (𝓤 ⁺)

  e' : A ≺⟨ 𝓐 ⟩ A
  e' = α , d

  γ' : 𝟘
  γ' = irrefl 𝓐 A e
-}
\end{code}

The uncommented version is a manually beta-reduced form of the
commented-out version.

Some corollaries follow.

The main work in the first one, which says that the type of all
ordinals is large, happens in the function transfer-structure, which
is developed in the module OrdinalsWellOrderTransport, where the
difficulties are explained.

As discussed above, the type OrdinalOfOrdinals 𝓤 of ordinals in the
universe 𝓤 lives in the next universe 𝓤⁺. We say that a type in the
universe 𝓤⁺ is small if it is equivalent to some type in 𝓤, and large
otherwise:

\begin{code}

is-small : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
is-small {𝓤} 𝓧 = Σ X ꞉ 𝓤 ̇ , X ≃ 𝓧

is-large : 𝓤 ⁺ ̇ → 𝓤 ⁺ ̇
is-large 𝓧 = ¬ is-small 𝓧

\end{code}

Our first corollary of Burali-Forti is that the type of ordinals is
large, as expected:

\begin{code}

the-type-of-ordinals-is-large : is-large (Ordinal 𝓤)
the-type-of-ordinals-is-large {𝓤} (X , 𝕗) = γ
 where
  δ : Σ s ꞉ OrdinalStructure X , (X , s) ≃ₒ OrdinalOfOrdinals 𝓤
  δ = transfer-structure fe X (OrdinalOfOrdinals 𝓤)
       𝕗 (_⊲⁻_ , ⊲-is-equivalent-to-⊲⁻)

  γ : 𝟘
  γ = Burali-Forti ((X , pr₁ δ) , pr₂ δ)

\end{code}

It is crucial in the above proof, in order to be able to transfer the
ordinal structure of the ordinal of ordinals to the type X along the
hypothetical equivalence 𝕗 : X ≃ Ordinal 𝓤, that the order _⊲_ has a
resized-down version _⊲⁻_ , as mentioned above.

By a *universe embedding* we mean a map

    f : 𝓤 → 𝓥

of universes such that

    f X ≃ X.

Of course, any two universe embeddings are equal, by univalence, so
that there is at most one universe embedding.

Moreover, universe embeddings are automatically type embeddings
(meaning that they have subsingleton fibers), as shown in the module
UF-UniverseEmbeddings.

So the following says that the universe 𝓤⁺ is strictly larger than the
universe 𝓤:

\begin{code}

successive-universe-embeddings-dont-have-sections : (f : 𝓤 ̇ → 𝓤 ⁺ ̇ )
                                                  → is-universe-embedding f
                                                  → ¬ has-section f
successive-universe-embeddings-dont-have-sections {𝓤} f i (s , η) = γ
 where
  X : 𝓤 ̇
  X = s (Ordinal 𝓤)

  p : f X ≡ Ordinal 𝓤
  p = η (Ordinal 𝓤)

  e : X ≃ Ordinal 𝓤
  e = transport (X ≃_) p (≃-sym (i X))

  γ : 𝟘
  γ = the-type-of-ordinals-is-large (X , e)


successive-universe-embeddings-are-not-equivs : (f : 𝓤 ̇ → 𝓤 ⁺ ̇ )
                                              → is-universe-embedding f
                                              → ¬ is-equiv f
successive-universe-embeddings-are-not-equivs f i j =
  successive-universe-embeddings-dont-have-sections f i
   (equivs-have-sections f j)

\end{code}

In particular, we have the following, where

  Lift {𝓤} (𝓤 ⁺) : 𝓤 → 𝓤⁺

is the canonical embedding of the universe 𝓤 into the successor
universe 𝓤⁺ defined in the module UF-UniverseEmbedding:

\begin{code}

Lift-doesnt-have-section : ¬ has-section (Lift {𝓤} (𝓤 ⁺))
Lift-doesnt-have-section {𝓤} h =
  successive-universe-embeddings-dont-have-sections
   (Lift (𝓤 ⁺)) (λ X → Lift-is-universe-embedding (𝓤 ⁺) X) h

Lift-is-not-equiv : ¬ is-equiv (Lift {𝓤} (𝓤 ⁺))
Lift-is-not-equiv {𝓤} e = Lift-doesnt-have-section
                           (equivs-have-sections (Lift (𝓤 ⁺)) e)
\end{code}

For a universe 𝓤, we define the type

    hSet 𝓤 : 𝓤⁺

of sets in the universe 𝓤 by

    hSet 𝓤 = Σ A ꞉ 𝓤 ̇ , is-set A.

By an *hSet embedding* we mean a map

    f : hSet 𝓤 → hSet 𝓥

such that the underlying type of f 𝕏 is equivalent to the
underlying type of 𝕏, that is,

    pr₁ (f 𝕏) ≃ pr₁ 𝕏,

for all 𝕏 : hSet 𝓤.

Any hSet-embedding is a type embedding, and any two hSet-embeddings
are equal by univalence. The map

    Lift-hSet {𝓤} (𝓤 ⁺) : hSet 𝓤 → hSet 𝓤⁺

is the unique hSet embedding, given by

    Lift-hSet 𝓥 (X , i) = Lift 𝓥 X , Lift-is-set X i)

where

    Lift-is-set X i : is-set (Lift 𝓥 X)

is derived from the fact that Lift 𝓥 X ≃ X using i : is-set X.

\begin{code}

Lift-hSet-doesnt-have-section : ¬ has-section (Lift-hSet {𝓤} (𝓤 ⁺))
Lift-hSet-doesnt-have-section {𝓤} (s , η) = γ
 where
  𝕐 : hSet (𝓤 ⁺)
  𝕐 = (Ordinal 𝓤 , type-of-ordinals-is-set)

  𝕏 : hSet 𝓤
  𝕏 = s 𝕐

  X : 𝓤 ̇
  X = pr₁ 𝕏

  p : Lift (𝓤 ⁺) X ≡ Ordinal 𝓤
  p = ap pr₁ (η 𝕐)

  d : X ≃ Lift (𝓤 ⁺) X
  d = ≃-sym (Lift-is-universe-embedding (𝓤 ⁺) X)

  e : X ≃ Ordinal 𝓤
  e = transport (X ≃_) p d

  γ : 𝟘
  γ = the-type-of-ordinals-is-large (X , e)

\end{code}

Finally, the following says that the type of sets in 𝓤⁺ is strictly
larger than that of sets in 𝓤, as we wanted to show:

\begin{code}

Lift-hSet-is-not-equiv : ¬ is-equiv (Lift-hSet {𝓤} (𝓤 ⁺))
Lift-hSet-is-not-equiv {𝓤} e = Lift-hSet-doesnt-have-section
                                (equivs-have-sections (Lift-hSet (𝓤 ⁺)) e)
\end{code}

This doesn't show that ¬ (hSet 𝓤 ≃ hSet 𝓤⁺), as in principle there may
be an equivalence that is not an hSet embedding in the sense defined
above, which we leave as an open problem. Notice that excluded middle,
which is not assumed but is consistent, implies that there is an
automorphism of hSet 𝓤 that swaps the empty set 𝟘 and the one-point
set 𝟙 and leaves all the other sets unchanged, so that potentially
there are automorphisms of hSet 𝓤 that are not hSet embeddings. We
don't know whether such a rogue equivalence hSet 𝓤 ≃ hSet 𝓤⁺ exists,
but this shouldn't be the case, of course.

Similarly, the above also doesn't show that ¬ (𝓤 ≃ 𝓤⁺), but we know
that this is the case by a different argument, which generalizes
Thierry Coquand's "paradox of trees", developed in the module
LawvereFPT.

Marc Bezem conjectures that ¬ (Σ A : 𝓤 ̇ , A ≃ ∥ 𝓤 ̇ ∥₀), that is, there
is no type in 𝓤 equivalent to the set truncation of 𝓤.
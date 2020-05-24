---
title: Simply typed lambda calculus
series: "Introduction to Type Systems"
---

Our exploration of type systems starts quite simple, with the *simply typed lambda calculus* (STLC).
This type system is the foundation of more complex type systems such as Haskell's.
The simply typed lambda calculus is based on the *(untyped) lambda calculus*.
To understand the simply typed lambda calculus, you do *not* have to understand the untyped lambda calculus, but it could be beneficial, as I will refer to some of its properties.
If you want to read about the untyped lambda calculus, the following articles might be helpful:

- [*Lambda Calculus* by Afnan Enayet](https://afnan.io/posts/lambda-calculus/)
- [*Lambda Calculus* by Ben Lynn](https://crypto.stanford.edu/~blynn/lambda/)

<details>
<summary>Imports etc.</summary>

> module SimplyTyped where
>
> import           Control.Monad   (when)
> import qualified Data.Map.Strict as Map
> import           Data.Map.Strict (Map)

</details>

Syntax
======

The syntax of a (programming) language describes how the language is written.
The syntax of the simply typed lambda calculus consists of two things: *terms* and *types*.

Types
-----

One major difference between the untyped lambda calculus and the simply typed, is that the latter has a notion of *types*.
The STLC contains two different sorts of types:

1. *Function types*.
   We write the type of a function that accepts a parameter of type $\tau$ and returns a value of type $\tau'$ as $\tau \rightarrow \tau'$.
   The identity function on booleans, for example, accepts a parameter of type $\mathsf{Bool}$ (boolean), and returns a value of the same type.
   Its type is thus written as $\mathsf{Bool} \rightarrow \mathsf{Bool}$.
   We also add that the function arrow is *right-associative*: $\tau \rightarrow \tau' \rightarrow \tau''$ is the same as $\tau \rightarrow (\tau' \rightarrow \tau'')$.
2. *Simple types* (also called *constant types*).
   These types are what makes the STLC the simply typed lambda calculus.
   The simple types are the types of the constant values: `True` has type `Bool` (boolean), `8` has type `Int` (integer), et cetera.

We can choose the simple types however we like.
Here, we'll use booleans and integers, and add the if-then-else construct and addition.
Adding operations like subtraction, multiplication, etc., is very straight-forward when you know how to handle addition, so I won't explicitly explain how they work.

In more formal syntax, we write:

$$
\begin{align*}
  \tau ::=\ & \tau \rightarrow \tau' & \text{(function type)} \\
      \mid\ & \mathsf{Bool} & \text{(boolean type)} \\
      \mid\ & \mathsf{Int} & \text{(integer type)}
\end{align*}
$$

You can read the symbol $::=$ as '*is defined by the following rules*'.
The symbol $\mid$ separates rules, and you can read it as '*or*'.
The grammar description starts with a $\tau$ (Greek letter tau, commonly used for denoting types);
whenever you see a $\tau$ or a $\tau$ with any number of primes (which are used to make clear that these types may differ), it means that the syntax 'expects' another type there.
The syntax of types is thus defined recursively.
(This notation of grammars is called [Backus-Naur form](https://en.wikipedia.org/wiki/Backus%E2%80%93Naur_form) (BNF).)

Translating such a syntax definition to Haskell is quite easy.
We define a type called `Type`, which contains the [*abstract syntax tree*](https://en.wikipedia.org/wiki/Abstract_syntax_tree) (AST) for types.
The AST does not directly correspond to the actual syntax of the types;
we don't encode in the AST how whitespace should be handled, how comments are written, that the function arrow is right-associative, etc.
That's why it's called an *abstract* syntax tree.
The Haskell data type for the AST of types looks like this:

> data Type
>   = TyFun Type Type
>     -- ^ Function type. The type @TyFun ty1 ty2@
>     -- corresponds to @ty1 -> ty2@.
>   | TyBool
>     -- ^ Boolean type
>   | TyInt
>     -- ^ Integer type
>   deriving (Show, Eq)

Terms
-----

There are five sorts of terms in the STLC.
These are based on the terms of the untyped lambda calculus, with some additions: the syntax for abstractions is a bit different and values and computation constructs are added.
The terms of the STLC consist of:

1. *Variables*.
   These are names for values.
   We generally use strings of characters as variable names, but we could just as well use integers[^De-Bruijn].

   What strings are valid variable names is not very important here, since we aren't writing a parser.
   Variable names generally consist of alphanumeric characters, starting with an alphabetic character.
   We'll use this as an informal rule.
2. *Abstractions*.
   Abstractions are functions.
   They accept one[^Multiple-parameters] parameter and return a value.
   We write them like in the untyped lambda calculus, but add the type of the parameter.

   The identity function on booleans, $\mathsf{id}_\mathsf{Bool}$, for example, is written like $\lambda x : \mathsf{Bool}. x$.
   (Or, in more Haskell-like syntax: `\x : Bool. x`.)
   This function accepts a boolean parameter named $x$.
   In the return value (which is written after the period), we can use the variable name $x$ to refer to the value that was *bound* (i.e., introduced) by the abstraction.
3. *Applications*.
   This is just function application.
   We write it using juxtaposition: $x$ applied to $f$ is written as $f\ x$.
   Applications only really make sense when the left value is an abstraction (or a term that evaluates to one).
4. *(Constant) values*.
   These are values like integers (`3`), booleans (`True`), characters (`'f'`) et cetera.
   These values cannot be evaluated any further, and are pretty useless on their own, so we also need:
5. *Computation constructs*.
   These are terms like conditionals (`if a then b else c`), binary operations (`x + y`), et cetera.
   The key aspect of these constructs is that they have some sense of computation: `if True then a else b` should evaluate to `a`, `5 + 6` should evaluate to `11`.
   We add these terms to the lambda calculus when adding simple types, because without them, we can't 'do anything' with the values we added.

[^De-Bruijn]:
  Using integers as variables is actually a well-known technique.
  It is useful for writing an evaluator of the lambda calculus, because it is a lot easier to define substitution that way.
  If you want to know more, read about [*De Bruijn-indices*](https://en.wikipedia.org/wiki/De_Bruijn_index).

[^Multiple-parameters]:
  Instead of having support for functions with multiple parameters, we choose to write functions that return other functions.
  A function that adds its two integer parameters, for example, is written like $\lambda a : \mathsf{Int}. \lambda b : \mathsf{Int}. a + b$.
  This is called [Currying](https://en.wikipedia.org/wiki/Currying).

More formally, we describe the grammar of terms as follows:

$$
\begin{align*}
  t ::=\ & \mathsf{False} & \text{(false)} \\
   \mid\ & \mathsf{True} & \text{(true)} \\
   \mid\ & n & \text{(integer)} \\
   \mid\ & x & \text{(variable)} \\
   \mid\ & \lambda x : \tau.\ t & \text{(abstraction)} \\
   \mid\ & t\ t' & \text{(application)} \\
   \mid\ & t + t' & \text{(addition)} \\
   \mid\ & \mathbf{if}\ t\ \mathbf{then}\ t'\ \mathbf{else}\ t'' & \text{(if-then-else)}
\end{align*}
$$

We write $x$ for variables, without explicitly defining what $x$ can be.
And for integers we write $n$, also without explicitly specifying what valid values of $n$ are.
That's because, as explained above, it doesn't really matter what set of strings we allow as variable names for reasoning about programs.
And it also doesn't matter that much whether we use 32-bit, 64-bit, signed, unsigned, or unbounded integers.

Again, writing the Haskell definition is quite easy:

> data Term
>   = TmTrue
>     -- ^ True value
>   | TmFalse
>     -- ^ False value
>   | TmInt Integer
>     -- ^ Integer value
>   | TmVar String
>     -- ^ Variable
>   | TmAbs String Type Term
>     -- ^ Abstraction. @TmAbs x ty t@ corresponds to @\x : ty. t@.
>   | TmApp Term Term
>     -- ^ Application
>   | TmAdd Term Term
>     -- ^ Addition
>   | TmIf Term Term Term
>     -- ^ If-then-else conditional
>   deriving (Show, Eq)

Examples
--------

Let's look at some examples.
The abstract syntax tree of the identity function on booleans, which we've seen before, is written like this in Haskell:

> tmIdBool :: Term
> tmIdBool = TmAbs "x" TyBool (TmVar "x")

Another example is the `not` function, which inverts its boolean argument: $\lambda x : \mathsf{Bool}. \mathbf{if}\ x\ \mathbf{then}\ \mathsf{False}\ \mathbf{else}\ \mathsf{True}$.
In Haskell:

> tmNot :: Term
> tmNot = TmAbs "x" TyBool (TmIf (TmVar "x") TmFalse TmTrue)

A function that adds its two arguments: $\lambda x : \mathsf{Int}. \lambda y : \mathsf{Int}. x + y$.
In Haskell:

> tmAdd :: Term
> tmAdd = TmAbs "x" TyInt (TmAbs "y" TyInt (TmAdd (TmVar "x") (TmVar "y")))

And its type, $\mathsf{Int} \rightarrow \mathsf{Int} \rightarrow \mathsf{Int}$, which is the same as $\mathsf{Int} \rightarrow (\mathsf{Int} \rightarrow \mathsf{Int})$, is in Haskell:

> tyAdd :: Type
> tyAdd = TyFun TyInt (TyFun TyInt TyInt)

Now we know the syntax of terms and types, we can move on to the relation between the two.

Type checking
=============

A type checker checks that all values are used correctly, i.e., that they have the right type.
Type checking is useful, because it can help us spot mistakes in our program.
Without a type checker, if we were to evaluate the expression $1 + \mathsf{True}$, the program would crash;
it does not make sense to add a boolean and an integer.
A type checker can prevent the program from crashing, because it will reject faulty programs before they are interpreted or compiled.

To express that a term has a certain type, we use a *typing judgement*.
The judgement will look something like this in mathematical notation: $\Gamma \vdash t : \tau$.
You can read it as: *the context $\Gamma$ entails that $t$ has type $\tau$*.

The *context* is a set of *bindings*: variables and their types.
Contexts are generally written like this:

- $\varnothing$ denotes the empty context;
- $\Gamma, x : \tau$ denotes the context $\Gamma$ extended with $x$ and its type $\tau$.

The context $\varnothing, x : \mathsf{Bool}, f : \mathsf{Bool} \rightarrow \mathsf{Int}$ contains two bindings: the boolean $x$ and the boolean-to-integer function $f$.

We can combine typing judgements to form *typing rules*.
We use [*inference rules*](https://en.wikipedia.org/wiki/Rule_of_inference) to make statements about how to reason about terms and types.
These inference rules consist of a number of premises, a horizontal bar, and the conclusion.
An example is *modus ponens*:

$$
  \frac{
    \begin{array}{c}
      A \\
      A \rightarrow B
    \end{array}
  }{
    B
  }
$$

You can read this as: *if we have $A$ and $A \rightarrow B$ *(if $A$ then $B$)*, then we conclude $B$.*

We use this notation for typing rules.
The most simple rules are the rules for boolean and integer values:

$$
  \text{T-True:}\ \frac{}{\varnothing \vdash \mathsf{True} : \mathsf{Bool}}
$$

T-True is the name of the rule.
This rule has no premises, and states that we can conclude in an empty context that $\mathsf{True}$ has type $\mathsf{Bool}$.

Instead of writing $\varnothing \vdash t : \tau$, the $\varnothing$ is usually omitted: $\vdash t : \tau$.
So, the rule for $\mathsf{False}$ is:

$$
  \text{T-False:}\ \frac{}{\vdash \mathsf{False} : \mathsf{Bool}}
$$

And the rule for integers:

$$
  \text{T-Int:}\ \frac{}{\vdash n : \mathsf{Int}}
$$

Now let's write some more complex rules.
To find the type of variables, we look them up in the context.
To denote that $x$ has type $\tau$ in $\Gamma$, we write: $x : \tau \in \Gamma$.
So, the rule for variables is:

$$
  \text{T-Var:}\ \frac{
    x : \tau \in \Gamma
  }{
    \Gamma \vdash x : \tau
  }
$$

The rule for abstractions looks like this:

$$
  \text{T-Abs:}\ \frac{
    \Gamma, x : \tau \vdash t : \tau'
  }{
    \Gamma \vdash \lambda x : \tau. t : \tau \rightarrow \tau'
  }
$$

To type check abstractions, we add $x : \tau$ to the context (because $t$ might use $x$) and check the type of $t$.
We then know that the abstraction takes an argument of type $\tau$ and has a return type of the type of $t$.

For applications, we need to have a term with a function type on the left side, that accepts an argument with the type of the right side:

$$
  \text{T-App:}\ \frac{
    \begin{array}{c}
      \Gamma \vdash t : \tau \rightarrow \tau' \\
      \Gamma \vdash t' : \tau
    \end{array}
  }{
    \Gamma \vdash t\ t' : \tau'
  }
$$

For an addition, we require that the two operands are both integers.
The type of the addition is then also an integer:

$$
  \text{T-Add:}\ \frac{
    \begin{array}{c}
      \Gamma \vdash t : \mathsf{Int} \\
      \Gamma \vdash t' : \mathsf{Int}
    \end{array}
  }{
    \Gamma \vdash t + t' : \mathsf{Int}
  }
$$

When typing if-then-else terms, we expect the condition to be a boolean, and the two arms to have the same type:

$$
  \text{T-If:}\ \frac{
    \begin{array}{c}
      \Gamma \vdash t_1 : \mathsf{Bool} \\
      \Gamma \vdash t_2 : \tau \\
      \Gamma \vdash t_3 : \tau
    \end{array}
  }{
    \Gamma \vdash \mathbf{if}\ t_1\ \mathbf{then}\ t_2\ \mathbf{else}\ t_3 : \tau
  }
$$

Using these rules, we can implement a type checker in Haskell.

Implementation
--------------

For the context, we'll use a `Map`:

> type Context = Map String Type

The function `typeOf` will determine the type of a term in a certain context, or will throw a type error.
Its type is:

> typeOf :: Context -> Term -> Either TypeError Type

<details>
<summary>The definition of `TypeError`</summary>
 
> data TypeError

The variable was not bound by an abstraction.
  
>   = UnboundVariable String

An operand of an addition term was not an integer.

>   | AdditionNonInteger Term Type

The condition of an if-then-else term is not a boolean.
  
>   | NonBooleanCondition Term Type

The arms of an if-then-else term have different types.
    
>   | ArmsOfDifferentType Term Type Term Type

A function is applied to an argument of the wrong type.

>   | ApplicationWrongArgumentType Term Type Term Type

A term of a non-function type is the left part of an application.

>   | ApplicationNotFunction Term Type
>   deriving (Show)

</details>

The rules for boolean and integer values are really easy to implement:

> typeOf ctx TmTrue    = Right TyBool
> typeOf ctx TmFalse   = Right TyBool
> typeOf ctx (TmInt n) = Right TyInt

We can implement T-Var with a simple lookup:

> typeOf ctx (TmVar x) =
>   case Map.lookup x ctx of
>     Nothing -> Left $ UnboundVariable x
>     Just ty -> Right ty

For abstractions, ...

> typeOf ctx (TmAbs x ty t) =

..., we add `x` with the type `ty` to the context, and determine the type of `t` in the new context, ...

>   let ctx' = Map.insert x ty ctx
>       ty'  = typeOf ctx' t

..., and return the function type from `ty` to `ty'`:
  
>    in TyFun ty <$> ty'

(Note that `TyFun ty <$> ty` is the same as:

< case typeOf ctx' t of
<   Left e    -> Left e
<   Right ty' -> Right (TyFun ty ty')

But using the fact that [`Either`] is a [`Functor`] allows us to use [`fmap`], or the infix version [`(<$>)`].
This is more succinct that an explicit `case`-`of`.)

For type checking applications, we use the fact that [`Either`] is a [`Monad`], and use the [`do`-notation]:

> typeOf ctx (TmApp t1 t2) = do

We first determine the types of `t1` and `t2`:

>   ty1 <- typeOf ctx t1
>   ty2 <- typeOf ctx t2

The type of `t1` should be a function type:

>   case ty1 of
>     TyFun ty11 ty12 ->

And the type of `t2` should be the same as `t1`'s argument's type, `ty11`:

>       if ty2 == ty11
>         then Right ty12
>         else Left $ ApplicationWrongArgumentType t1 ty1 t2 ty2

If `t1` doesn't have a function type, then we can't apply it:

>     _ -> Left $ ApplicationNotFunction t1 ty1

For addition, if the two operands are integers, then the result is too:

> typeOf ctx (TmAdd t1 t2) = do
>   ty1 <- typeOf ctx t1
>   when (ty1 /= TyInt) $
>     Left $ AdditionNonInteger t1 ty1
>   ty2 <- typeOf ctx t2
>   when (ty2 /= TyInt) $
>     Left $ AdditionNonInteger t2 ty2
>   Right TyInt

We can also prevent duplication:

< typeOf ctx (TmAdd t1 t2) = do
<   check t1
<   check t2
<   Right TyInt
<   where
<     check t = do
<       ty <- typeOf ctx t
<       when (ty /= TyInt) $
<         Left $ AdditionNonInteger t ty

When type checking if-then-else terms, we want the condition to be a boolean, and the arms to be of the same type:

> typeOf ctx (TmIf t1 t2 t3) = do
>   ty1 <- typeOf ctx t1
>   when (ty1 /= TyBool) $
>     Left $ NonBooleanCondition t1 ty1
>   ty2 <- typeOf ctx t2
>   ty3 <- typeOf ctx t3
>   when (ty2 /= ty3) $
>     Left $ ArmsOfDifferentType t2 ty2 t3 ty3
>   Right ty2

And that's it!
We've now implemented our type checker.
Let's try it!

[`Either`]: https://hackage.haskell.org/package/base/docs/Prelude.html#t:Either
[`Functor`]: https://hackage.haskell.org/package/base/docs/Prelude.html#t:Functor
[`fmap`]: https://hackage.haskell.org/package/base/docs/Prelude.html#v:fmap
[`(<$>)`]: https://hackage.haskell.org/package/base/docs/Prelude.html#v:-60--36--62-
[`Monad`]: https://hackage.haskell.org/package/base/docs/Prelude.html#t:Monad
[`do`-notation]: https://wiki.haskell.org/Keywords#do

Examples
--------

Let's start with some terms we have already defined.
The type of the identity function on booleans, $\mathsf{id}_\mathsf{Bool}$, is:

< typeOf Map.empty tmIdBool
<   => Right (TyFun TyBool TyBool)

We see that type checking has been successful, since we've got a `Right` value back.
And the type is indeed what we were expecting: $\mathsf{Bool} \rightarrow \mathsf{Bool}$.

Let's also define the identity functions on boolean-to-integer functions:

> tmIdBoolToInt :: Term
> tmIdBoolToInt = TmAbs "f" (TyFun TyBool TyInt) (TmVar "f")

We expect its type to be $(\mathsf{Bool} \rightarrow \mathsf{Int}) \rightarrow (\mathsf{Bool} \rightarrow \mathsf{Int})$, and indeed:

< typeOf Map.empty tmIdBoolToInt
<   => Right (TyFun (TyFun TyBool TyInt) (TyFun TyBool TyInt))

The type of $\mathsf{not}$ should be $\mathsf{Bool} \rightarrow \mathsf{Bool}$:

< typeOf Map.empty tmNot
<   => Right (TyFun TyBool TyBool)

And the type of $\mathsf{add}$ should be $\mathsf{Int} \rightarrow \mathsf{Int} \rightarrow \mathsf{Int}$:

< typeOf Map.empty tmAdd
<   => Right (TyFun TyInt (TyFun TyInt TyInt))

So far, so good.
Let's also take a look at terms that should be rejected.

We expect our type checker to reject the term $\mathsf{True} + 1$, since we can't add booleans and integers:

< typeOf Map.empty (Middy TmTrue (TmInt 1))
<   => Left (AdditionNonInteger TmTrue TyBool)

Hurray, one mistake prevented!

We can't refer to variables that are not bound:

< typeOf Map.empty (TmVar "x")
<   => Left (UnboundVariable "x")

But if the variable is defined in the context, that should be no problem:

< typeOf (Map.fromList [("x", TyInt)]) (TmVar "x")
<   => Right TyInt

We should also reject $\mathsf{not}\ 14$, because $\mathsf{not}$ expects a boolean parameter:

< typeOf Map.empty (TmApp tmNot (TmInt 14))
<   => Left
<       (ApplicationWrongArgumentType
<         (TmAbs "x" TyBool (TmIf (TmVar "x") TmFalse TmTrue))
<         (TyFun TyBool TyBool)
<         (TmInt 14)
<         TyInt)

It would be nice to display these errors more user-friendly, but that's left as an exercise to the reader!

Let's try applying to a non-function value:

< typeOf Map.empty (TmApp TmFalse (TmInt 21))
<   => Left (ApplicationNotFunction TmFalse TyBool)

And if-then-else terms with a non-boolean condition:

< typeOf Map.empty (TmIf (TmAbs "x" TyBool (TmInt 0)) (TmInt 3) (TmInt 4))
<   => Left
<        (NonBooleanCondition
<          (TmAbs "x" TyBool (TmInt 0))
<          (TyFun TyBool TyInt))

Or with non-matching arms:

< typeOf Map.empty (TmIf TmTrue (TmInt 10) TmFalse)
<   => Left (ArmsOfDifferentType (TmInt 10) TyInt TmFalse TyBool)

Conclusion
==========

We've written a type checker for the simply typed lambda calculus!

If you want to a play a bit more with this type checker, you might want to do one of the following exercises, which I highly suggest:

1. Add other binary operators on integers, such as subtraction, multiplication, etc.
   Extend the abstract syntax, write the typing rules for these terms and extend the type checker to follow these rules.
2. Add support for another simple type, such as characters or strings.
   Extend the abstract syntax, write the typing rules and extend the type checker.
   Also add some computation constructs that interact with these values:
   for characters for example, you might want to add functions like Haskell's [`ord :: Char -> Int`](https://hackage.haskell.org/package/base/docs/Data-Char.html#v:ord) and [`chr :: Int -> Char`](https://hackage.haskell.org/package/base/docs/Data-Char.html#v:chr).
3. Write an evaluator for the STLC.
4. Write a parser for STLC terms.
   You might want to take a look at [Parsec](https://hackage.haskell.org/package/parsec), or find an introduction to *parser combinators*.
5. Rewrite the type checker using [monad transformers](https://hackage.haskell.org/package/mtl).
   The type checker can be written in the `ReaderT Context (Except TypeError)` monad.
   [*Learn You a Haskell for Great Good*](http://learnyouahaskell.com) has an [introduction to monad transformers](http://learnyouahaskell.com/for-a-few-monads-more).

In the next post, I'll describe how we can add more support for abstraction to the simply typed lambda calculus, and we'll take a look at *System F*.

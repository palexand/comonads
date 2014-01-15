\documentclass[10pt]{article}

%include lhs2TeX.fmt
%include lhs2TeX.sty

%format phi = "\Varid{\phi}"
%format phi1 = "\Varid{\phi_1}"
%format phi2 = "\Varid{\phi_2}"
%format phi3 = "\Varid{\phi_3}"
%format eval1 = "\Varid{eval}_1"
%format eval2 = "\Varid{eval}_2"
%format eval3 = "\Varid{eval}_3"
%format Expr1 = "\Varid{Expr}_1"
%format Expr2 = "\Varid{Expr}_2"
%format Expr3 = "\Varid{Expr}_3"
%format E1 = "\Varid{E}_1"
%format E2 = "\Varid{E}_2"
%format E3 = "\Varid{E}_3"
%format evalE = "\Varid{eval}_E"
%format mapE = "\Varid{map}_E"
%format phiE = "\Varid{\phi}_E"
%format test0 = "\Varid{test}_0"
%format test1 = "\Varid{test}_1"
%format test2 = "\Varid{test}_2"
%format test3 = "\Varid{test}_3"
%format test4 = "\Varid{test}_4"
%format test5 = "\Varid{test}_5"
%format test6 = "\Varid{test}_6"
%format test7 = "\Varid{test}_7"
%format test8 = "\Varid{test}_8"
%format test9 = "\Varid{test}_9"
%format test10 = "\Varid{test}_{10}"

\usepackage{fullpage}
\usepackage{alltt}

\bibliographystyle{plain}

\parskip=\medskipamount
\parindent=0pt

\title{A Haskell Companion to ``The Essence of Dataflow Programming''}
\author{\emph{Uk'taad B'mal} \\
  The University of Kansas - ITTC \\
  2335 Irving Hill Rd, Lawrence, KS 66045 \\
  \texttt{lambda@@ittc.ku.edu}}

\begin{document}

\maketitle

Before we start, everyone is to repeat to themselves the following
mantra:

\begin{quote}
  A (co)monad is a computation.  (co)unit and (co)bind operate on the
  computation but do not perform it.  (co)unit defines the value space
  for comonad evaluation.  (co)bind is in effect a Functor over
  (co)monads.
\end{quote}

The operator used for constructing the |LVS| monad from the |LV| monad
and |Stream| monad causes lhs2TeX fits.  So, it's been replaced with
|:!| throughout.

\begin{code}

module EssenceDF where

import qualified Data.List

\end{code}

\subsection*{The Comonad Class}

The basic structure of a comonad is embodied in the |Comonad| class.
Each comonad must have a |counit| and |cobind| function that
correspond with |return| and |bind| in the |Monad| class.  |counit|
accepts a comonad instance and returns the value encapsulated by the
comonad.  It is, in essence, the opposite of |return| from the |Monad|
class.  The |cobind| function accepts a function from the comonad type
to some value type, a comonad and returns a comonad over the value
type.

\begin{code}
class Comonad d where
    counit :: d a -> a
    cobind :: (d a -> b) -> d a -> d b

cmap :: Comonad d => (a -> b) -> d a -> d b
cmap f = cobind (f . counit)
\end{code}

\subsection*{The Id Comonad}

The |Id| comonad is the simplest comonad.  |counit| simply returns the
value encapsulated by |Id|.  |cobind| pushes the function |k| inside
the comonad |Id|.

\begin{code}
data Id a = Id a

instance Comonad Id where
    counit (Id a) = a
    cobind k d = Id (k d)
\end{code}

\subsection*{The Product Comonad}

Life gets more interesting with the product comonad, |Prod|.

Note that |e| is never evaluated by |cobind| or |counit|.  The
|counit| observer simply returns the first value.  The |cobind|
observer creates a new product from the result of calling |k| over the
argument comonad and composing it the the second product value, |e|.
The only thing that makes this interesting is that |e| is never
evaluated and can be infinite.

|askP| does access the second product element and thus must evaluate
it.  |localP| pushes a function inside the second product value.
However, it is once again not evaluated.  It appears that |askP| and
|localP| provide a mechanism for accessing the second element and
replacing the second element locally with a function over the second
element.  This would appear to be something like a |Writer| comonad.

\begin{code}
data Prod e a = a :& e

instance Comonad (Prod e) where
    counit (a :& _) = a
    cobind k d@(_ :& e) = (k d) :& e

askP :: Prod e a -> e
askP (_ :& e) = e

localP :: (e -> e) -> Prod e a -> Prod e a
localP g (a :& e) = a :& (g e)
\end{code}

\subsection*{The Stream Comonad}

The |Stream| comonad is much like |Prod| with the stream tail having
more specific properties.  Any stream is a current value, |a|
and the rest of the stream |az|.  Like the |Prod| comonand, |counit|
only references |a| and does not evaluated the rest of the stream.
|cobind| evaluates the current stream using |k| like |Prod|.  However,
the rest of the resulting stream is |(cobind k az)| pushing |k| down
to the remaining elements of the stream.

\begin{code}
data Stream a = a :< (Stream a) deriving Show

instance Comonad Stream where
    counit (a :< _) = a
    cobind k d@(_ :< az) = (k d) :< (cobind k az)

nextS :: Stream a -> Stream a
nextS (a :< az) = az

takeS :: Int -> Stream a -> [a]
takeS 0 _ = []
takeS (i + 1) (a :< az) = a : takeS i az

str2fun :: Stream a -> Int -> a
str2fun (a :< az) 0 = a
str2fun (_ :< az) (i + 1) = str2fun az i

fun2str :: (Int -> a) -> Stream a
fun2str f = fun2str' f 0
    where fun2str' f i = (f i) :< (fun2str' f (i + 1))

\end{code}

\subsection*{The LVS Comonad}

The LVS Comonad represents a process that consumes input from a
stream, |s|, produces a current value, |v|, and records its past in a
list, |l|.  Thus, the title |LVS|.  The comonad is defined by starting
with a custom |List| and composing it with a value to define |LV|.
The result is composed with a |Stream| to complete the |LVS| data
type.

An |LVS| value is thus define as:

\begin{spec}
  l := v :! s
\end{spec}

where |:=| and |:!| are infix constructors for
|LV| and |LVS| respectively.

\begin{code}
data LVS a = (LV a) :! (Stream a)
\end{code}

To make |LVS| a comonad, we must define |counit| and |cobind| as
required by the |Comonad| typeclass.  |counit :: (c a) -> a| is define
as one would expect, extracting the value from the |LVS| structure and
returning it.

|cobind| is a bit more involved, but not substantially more complex.
The function defines its value by composing |(cobindL lvs)|, |(k lvs)|
and |(cobindS lvs)| where |lvs| is the current |LVS| instance and
|cobindL| and |cobindS| are local helper functions for generating the
new |List| and |Stream| values.  So, |cobind| is simply defined as:

\begin{spec}
  (cobindL d) := (k d) :! (cobindS d)
\end{spec}

\begin{code}
instance Comonad LVS where
    counit (past := a :! future) = a
    cobind k d = cobindL d := (k d) :! cobindS d
        where cobindL (Nil          := a :! future) = Nil
              cobindL (past' :> a'  := a :! future) = cobindL d' :> k d'
                  where d' = past' := a' :! (a :< future)
              cobindS (past := a :! (a' :< future')) = k d' :< cobindS d'
                  where d' = past :> a := a' :! future'
\end{code}

Taking a look at |cobindL| and |cobindS| reveal how the new |LVS|
structure is defined.  |cobindL| has two cases, one for each |List|
constructor.  The first says that if |past| is |Nil|, then it remains
|Nil| in the new |LVS| structure.

In the case for |past' :> a'| we're going to create a new past by
recursively calling |cobindL|.  The value of |d'| is a one-step
unwinding of the previous |past| value.  Specifically, |past' := a'|
is the value of |past| and |v| before |a| was added.  |(a' :< future)|
is the value of |future| before |a| was processed.  What is happening
is that the entire |past| list is regenerated each time new |future|
element is processed.  Furthermore, elements of |past| appear to be
the entire comonad representing past states.

|cobindS| is quite similar with the |future| generated.  Here, |d'|
represents the current comonad value with the first element of
|future| bound to |a'| and the current value added to the current
|past|.  In effect, we are remembering the current value while
preparing the next value.  |cobindS| is called on |d'|.  |k d'| is
added to |cobindS d'| to add the processing of the current |LVT| value
to the future stream.

The question is why keep track of all this stuff?  |past| seems to be
every comonad, not just value, that has been seen.  |future| seems to
be a stream of every value generated followed by a computation
representing future values.  This seems rather redundant.

\begin{code}
runLVS :: (LVS a -> b) -> Stream a -> Stream b
runLVS k (a' :< as') = runLVS' k (Nil := a' :! as')
                       where runLVS' k d@(az := a :! (a' :< as')) = (k d) :< (runLVS' k (az :> a := a' :! as'))

fbyLVS :: a -> (LVS a -> a)
fbyLVS a0 (Nil := _ :! _)  = a0
fbyLVS _ ((_ :> a') := _ :! _) = a'

nextLVS :: LVS a -> a
nextLVS (_ := _ :! (a :< _)) = a

showLVS :: (Show a) => LVS a -> IO ()
showLVS (Nil := a0 :! future) = (putStr . show) a0 >> putStr ", " >> showLVS' future
    where showLVS' (a' :< as') = (putStr . show) a' >> putStr ", " >> showLVS' as'
\end{code}

\subsection*{The LV Comonad}

The paper presents the LVS comonad first and the LV comonad later.  I
find it much easier to approach the LVS comonad if you look at LV
first, however I understand why they did this and will discuss that in
the context of |runLV|.  The data structure for the |LV| comonad is a
product composed of a list and a value.  The contents of the list and
the value are the same type.  The single constructor is |:=| forms the
product.  It is simpler for some people to think about the LV comonad
as simply a pair rather than using the infix constructor.  Your
mileage may vary.\footnote{I moved the code for the LV comonad here
  from the LVS definition}

\begin{code}
data List a = Nil | (List a) :> a deriving Show

data LV a = (List a) := a
\end{code}

To make the |LV| data type a comonad, we must define |counit| and
|cobind|.  |counit|, like |unit| for a monad, simply returns the
comonad value.  As the name implies, it is the dual of |unit|,
returning a value from an encapsulated value rather than encapsulating
a given value.  |cobind| is a mapping or functor over |LV| as it is
for any comonad.  This is important to remember as we get rolling -
|cobind| operates on comonadic computation but does not perform the
evaluation.  |cobind| is defined by forming the product of |cobind k
past| and |k d| where |d| is the current |LV| value and |k| is a
function we want to push into the comonad.

Given all this, |k d| is the next |V| and |cobindL k past| is the next
history list.  By applying |k| to the current |LV| instance we get a
new value of type |b| from the original value of type |LV a|.
Remember that the type contained in |L| must be the same type as |V|.
Thus, whatever we do to |L a| it must result in something of type |L
b|.

|cobindL k past| is the next history list.  Remember that |L| must
contain items of the same type is |V|.  Thus, whatever we do to |L| of
type |List a|, we have to end up with something of type |List b|.
Looking at the definition of |Comonad| reminds us that |k| has type |d
a -> b| where |d| is the comonad constructor.  If |L| contains things
of type |d a| then cobind is just a kind of fold or map with respect
to the comonad structure.  Specifically, |cobind k L| is of type |List
b| if |L| is of type |List (d a)|.  In this case, |d| is |LV|.  So,
the history is a list of |LV| comonads representing past computations.
So far, so good.

\begin{code}
instance Comonad LV where
    counit (_ := a) = a
    cobind k d@(past := _) = cobindL k past := (k d)
        where cobindL k Nil = Nil
              cobindL k (past :> a) = cobindL k past :> (k (past := a))
\end{code}

|cobind| is a map, so let's define it like a map with a base case and
a recursive case.  Looking at the implementation, that's exactly what
is done.  |cobindL| is defined for both cases of the |List|
constructor.  |cobindL Nil = Nil| indicating the end of the history
list.  Basically, |Nil| represents the beginning of execution and the
termination of the recursive |combindL| function.

|cobindL k (past :> a)| defines the case when there is a nonempty past
to push the cobind through.  |cobindL k past| takes care of the
recursion and will terminate when |Nil| is encountered.  |k| requires
an |LV| comonad, thus one is formed using |:=| to combine |past| with
|a|.  Notice that |past| is the argument to |cobindL| with the most
recent element, |a| removed.  Thus, |past := a| is the previous
comonad and |(k (past := a))| is performing the mapping operation.
The recursive call to |cobindL k past| steps through each element of
the history list, creates a comonad and calls |k| on it.

|runLV| performs the computation defined by a comonad.  The first
argument is a function from |LV a| to |b|.  The |k| mapped into the
comonad by |cobind| will be instantiated with this function when the
comonad is evaluated.  Think about the cobind as setting up a
structure for evaluating |k| across the entire comonad.  The second
argument is a stream of inputs inputs.  Evaluating the comonad results
in a stream of outputs.

\begin{code}
runLV :: (LV a -> b) -> Stream a -> Stream b
runLV k (a' :< as') = runLV' k (Nil := a' :! as')
    where runLV' k (d@(az := a) :! (a' :< as')) = (k d) :< runLV' k (az :> a := a' :! as')
\end{code}

The bulk of |runLV| is defined by a helper |runLV'| that turns the
|LV| comonad into an |LVS| comonad.  I commented earlier that
understanding the |LV| comonad is easier than |LVS|.  The definition
of |runLV| is why |LVS| is presented first.  The initial |LVS| comonad
is defined from the |LV| comonad in the following way:

\begin{spec}
  (Nil := a' :! as')
\end{spec}

where |a'| is the first element of the input stream and |as'| is the
rest of the stream.  Thus, the |LVS| comonad starts with no past, with
the first stream element as the value and remaining stream elements as
the future.  What's interesting here is that the instantiated |LVS|
uses the input stream type as the future type.  This correctly
suggests that the |runLVS| function will not be used to evaluate the
|LV| comonad.  I would suspect that it could, but that is left as an
exercise for the reader.

|runLV'| is remarkably straightforward given where we've already been.
|k| is the function to evaluate, |d| is the original |LV| comonad
split into |az| and |a| by pattern matching.  |a'| is the current head
of the input stream and |as'| is th rest of the stream.  |runLV'| is
then a stream where |(k d)| is the head.  So, the current |LV| comonad
is evaluated by |k| giving us something of type |b| just as we would
expect.  |runLV'| is called recursively to generate the rest of the
stream.  The new past is |az| with |a| added.  The new value is |a'|,
the first element of the current input stream.  The new future is
|as'|, the rest of the input stream.  What this implements is a
mapping of |k| onto the input stream to generate an output stream.
Exactly what we want.

The |fbyLV| function is a utility function that is pronounced
``followed by'' and implements exactly that function.  Given a value
|a0| of type |a| and an |LV| comonad |(past := v)|, |v| is followed by
|a0| if |past| is empty.  If |past| is not empty, then |v| is followed
by the last element in |past|.

\begin{code}
fbyLV :: a -> (LV a -> a)
fbyLV a0 (Nil := _) = a0
fbyLV _ ((_ :> a') := _) = a'
\end{code}

The following are examples of using |LV| to evaluate a function over a
stream.  |incLV| is a simple function that increments the value from
the input stream.  It does not depend on the past in any way, so we
need only a single case that ignores the past.

\begin{code}
incLV :: LV Integer -> Integer
incLV (_ := x) = x+1
\end{code}

|sumLV| is similar to |incLV| except that it adds the input stream
value to the previous input stream value.  What is very interesting to
note is that the input stream value is save in |past|, not the
generated sum value.  If we want to save a new state, then it may be
necessary to modify the |LV| comonad or the |runLV| function.  This
example shows one way of looking into the past.

\begin{code}
sumLV :: LV Integer -> Integer
sumLV (Nil := x) = 0+x
sumLV ((_ :> y) := x) = y + x
\end{code}

|andLV| operates on two streams of boolean values zipped together.  In
effect, these are the inputs to an and gate. The output is the result
of conjuncting the boolean values.  This example shows one way of
dealing with multiple inputs.

\begin{code}
andLV :: LV (Bool,Bool) -> Bool
andLV (_ := (x,y)) = x && y
\end{code}

The most confusing thing about using |runLV| now that we have it is
generating streams.  Basically, there is no designator for the initial
or first stream.  With |List|, you start with |Nil| and build up the
list.  With |Stream| there is no |Nil| resulting in infinite things.
|intStream| and |boolStream| are infinite streams of 1 and |True|
respectively.  Note that test cases for the interpreter below contain
similar functions for generating infinite streams of things.

\begin{code}
intStream = 1 :< intStream
boolStream = True :< boolStream
\end{code}

The infinite streams can be input into the |runLV| function directly,
but it's more interesting to put values in front of the infinite tail.
Some examples of this include adding 1 to the stream
$1,2,3,0,1,1,1,...$:

\begin{spec}
runLV incLV (1 :< (2 :< (3 :< (4 :< (0 :< intStream)))))
\end{spec}

\noindent adding pairs of values $0+1,1+2,2+3,3+4,4+0,0+1,1+1,$...:

\begin{spec}
runLV sumLV (1 :< (2 :< (3 :< (4 :< (0 :< intStream)))))
\end{spec}

\noindent and running an ``and'' gate through it's possible inputs.
You might want to evaluate the |zipS| separately to see the zip
operation on streams.  (I really think that |Stream| should be an
instance of |ComonadZip| rather than use a separate function):

\begin{spec}
runLV andLV (zipS (True :< (False :< (True :< (False :< boolStream))))
                  (True :< (True :< (False :< (False :< boolStream)))))
\end{spec}

One interesting observation is that |runLV2| operating on |sumLV| does
not keep a running sum of the values in its past list.  Initially,
this is what I had hoped it would do.  However, it's an easy
modification to |runLV| to store the system state rather than the
previous input.  |runLV2| does exactly this.  The |let| variable |kd|
references |(k d)| and is added to the past list.  Thus, then the next
input is processed, it is added to the past value rather than the past
input.

\begin{code}
runLV2 :: (LV a -> a) -> Stream a -> Stream a
runLV2 k (a' :< as') = runLV' k (Nil := a' :! as')
    where runLV' k (d@(az := a) :! (a' :< as')) =
              let kd = (k d) in 
              kd :< runLV' k (az :> kd := a' :! as')
\end{code}

You can run |sumLV| using |runLV2| to see the difference in the output.

\begin{spec}
runLV2 sumLV (1 :< (2 :< (3 :< (4 :< (0 :< intStream)))))
\end{spec}

Note that the paper defines a proper sum function that uses |sumLV|
that we will examine later.

The biggest problem here is that none of these examples halt.  The
input stream is infinite in each case, thus no termination.  The
utility function |takeS| solves this problem by defining a |take|
function over streams.  |takeS i s| takes the first |i| elements from
stream |s| and returns them as a list.  Thus:

\begin{spec}
take 5 (runLV incLV (1 :< (2 :< (3 :< (4 :< (0 :< intStream))))))
\end{spec}

will generate a list:

\begin{spec}
[2,3,4,5,1]
\end{spec}

This should make testing quite a bit simpler.

\subsection*{Comonadic Zip}

The |ComonadZip| class defines a function over a comonad that zips two
comonads into a single comonand.  The two comonads must be instances
of the same class, but may encapsulate things of different types.  The
resulting type is an instance of the comonad class defined over the
product of the originally encapsulated types.  The function signature
pretty much says it all.

\begin{code}
class Comonad d => ComonadZip d where
    czip :: d a -> d b -> d (a, b)
\end{code}

Examples of |ComonadZip| are included for |Id|, |LVS| and |LV|.  |Id| is
quite simple with |czip| extracting comonad values, forming a
product, and injecting the product back into |Id|.

\begin{code}
instance ComonadZip Id where
    czip (Id a) (Id b) = Id (a, b)
\end{code}

|czip| for |LVS| and |LV| is not much more complicated.  |zipL| takes
care of zipping two lists together.  Defined recursively, |zipL| forms
the product of the first two |List| elements and adds that to zipping
the remainder of the lists together.  Note that zip ends when
\emph{either} list is empty.

\begin{code}
zipL :: List a -> List b -> List (a, b)
zipL Nil _ = Nil
zipL _ Nil = Nil
zipL (az :> a) (bz :> b) = (zipL az bz) :> (a, b)
\end{code}

|zipS| for |Stream| is analogous to |zipL|.  The product of the
current stream values is added to zipping the remainder of the streams
together.

\begin{code}
zipS :: Stream a -> Stream b -> Stream (a, b)
zipS (a :< az) (b :< bz) = (a, b) :< (zipS az bz)
\end{code}

With |zipS| and |zipL| defined, |czip| for |LVS| is quite simple.
|zipL| combines the past lists, |zipS| combines the future streams,
and product combines the current values.

\begin{code}
instance ComonadZip LVS where
    czip (past := a :! future) (past' := b :! future') = zipL past past' := (a, b) :! zipS future future'
\end{code}

|czip| for |LV| the same as |LVS| except that there is no future to
zip together and add to the result.  Same utility functions used in
the same way.

\begin{code}
instance ComonadZip LV where
    czip (past := a) (past' := b) = zipL past past' := (a, b)
\end{code}

\subsection*{A Comonadic Interpreter}

Among the most useful applications of monads is interpreter
construction.  Similarly, it appears, for comonads.

The data structure for the language AST remains unchanged from most
monadic language ASTs.  Note that this is not a composable AST due to
its recursive nature.  First define structures for th term space and
the value space.  In a monadic interpreter, the language elements are
instances of |Monad| while values are basic Haskell types.  Note here
that terms are a constructed type while values are comonads.

\begin{code}
type Var = String

data Tm = V Var | L Var Tm | Tm :@ Tm | Rec Tm
        | N Integer | Tm :+ Tm | Tm :- Tm | Tm :* Tm | Mod Tm Tm
        | Tm :== Tm | Tm :/= Tm | TT | FF | Not Tm | Tm :&& Tm
        | If Tm Tm Tm
        | Next Tm
        | Fby Tm Tm
\end{code}

The value space consists of integers, booleans and functions.  |Val|
is parameterized over a comonad, |d| making the resulting
values comonadic.  Of particular interest is the definition of |F|, a
comonadic function.  Specifically, a |F| encapsulates a mapping from a
comonadic value |d (Val d)| to a value |Val d|.  Note that |Val d| is
not comonadic but must know about the comonad because can be a
function value.

\begin{code}
data Val d = I Integer | B Bool | F ( d (Val d) -> Val d )

instance Show (Val d) where
    show (I i) = show i
    show (B b) = show b
    show (F f) = "Func"
\end{code}

An environment is simply a list of |Var|, |Val| pairs where |Var| is a
string type and |Val d| is simply a value as defined above.  Neither
|Env| or |Val d| are comonadic, but again must know about the comonad
to define function values.

\begin{code}
type Env d = [(Var,Val d)]
\end{code}

A an instance |ComonadEv| must have an evaluation function, |ev|, that
accepts a term, a comonadic environment, and generates a value.  |Env
d| is not a comonad, but |d (Env d)| definitely is.  Thus, it
minimally has a cobind for applying operations and a counit for
returning the environment value.

\begin{code}
class ComonadZip d => ComonadEv d where
    ev :: Tm -> d (Env d) -> Val d
\end{code}

The |ev'| function is a helper for defining interpreters.  It is, in
essence, an interpeter core that implements basic $\lambda$-caculus
style functions for operations, $\lambda$ definition and application,
and variable usage.  The signature defines |ev'| as a function from a
term and comonadic environment to a value.  This should be expected.
The comonad, |d|, must be an instance of |ComonadEv| having an |ev|
function defined for function evaluation.

\begin{code}
ev' :: ComonadEv d => Tm -> d (Env d) -> Val d
\end{code}

|V| is the variable constructor and is evaluted by looking it's value
up in the environment.  |counit| extracts the environment from the
current environment, |denv|.  |unsafeLookup| then calls the standard
|lookup| function with the variable name and the environment's value.

\begin{code}
ev' (V x)         denv = unsafeLookup x (counit denv)
\end{code}

|L| defines a lambda that when evaluated results in a function value.
This definition is remarkably like the definition used in monadic
interpreters in that a Haskell fuction is used to represent the
evaluation.  The expression, |e|, is evaluated in the context of the
comonadic environment |denv| with the comonadic value |d| added to it.

|d| is instantiated when the function value is used, thus it
represents the comonadic value the function is applied to.  The
Haskell function representing the fucntion value calls |ev e| to
evaluate the expression encapsulated by |L| in an environment with |d|
associated with the variable name |x|.  The trick is generating the
environment.

|d| is first zipped together with |denv| resulting in a comonad of
value, environment pairs.  |repair| (``re-pair'' not fix) takes an
value, environment pair and creates an evironment buy: (i) pairing |x|
with the value; and (ii) consing the pair onto the environment.
Using |cmap| to apply |repair| to each value, environment pair
effectively adds the new binding.

\begin{code}
ev' (L x e)       denv = F (\ d -> ev e (cmap repair (czip d denv)))
    where repair (a, env) = (x, a) : env
\end{code}

The |e :@ e'| function application syntax uses cobind to apply the
evaluation of |e'| to then environment and calles the function value
resulting from evaluating |e| to the result.  The case expression
evaluates |e| in |denv| and attempts to extract a function value from
the result.  |cobind| is then used to apply |(ev e')| to the original
environment.  Finally, calling |f| evaluates the encapsulated function
expression in the context of the new environment.

\begin{code}
ev' (e :@ e')     denv = case ev e denv of
                           F f -> f (cobind (ev e') denv)
\end{code}

The |Rec| constructor provides a mechanism for evaluating recursive
operations.  Specifically, it uses the definition of fixed-point to
perform one-step expansion of a recursive function application.  Note
that cobind is called on |ev'| of |Rec e| giving us the desired
recursive effect.

\begin{code}
ev' (Rec e)       denv = case ev e denv of
                           F f -> f (cobind (ev' (Rec e)) denv)
\end{code}

The following cases implement operations over integers and booleans.
In each case, arguments to the operator are evaluated in the current
environment.  If they are the correct type, then an operation from the
host language is used to calculate a new value that is then returned.

\begin{code}
ev' (N n)         denv = I n
ev' (e0 :+ e1)    denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> I (n0 + n1)
ev' (e0 :- e1)    denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> I (n0 - n1)
ev' (e0 :* e1)    denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> I (n0 * n1)
ev' (Mod e0 e1)   denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> I (n0 `mod` n1)
ev' (e0 :== e1)   denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> B (n0 == n1)
                           B b0 -> case ev e1 denv of
                                     B b1 -> B (b0 == b1)
ev' (e0 :/= e1)   denv = case ev e0 denv of
                           I n0 -> case ev e1 denv of
                                     I n1 -> B (n0 /= n1)
                           B b0 -> case ev e1 denv of
                                     B b1 -> B (b0 /= b1)
ev' TT            denv = B True
ev' FF            denv = B False
ev' (Not e)       denv = case ev e denv of
                           B b -> B (not b)
ev' (e0 :&& e1)   denv = case ev e0 denv of
                           B b0 -> case ev e1 denv of
                                     B b1 -> B (b0 && b1)
\end{code}

|If| is defined in the classic, functional fashion as an expression
rather than a statement.

\begin{code}
ev' (If e e0 e1)  denv = case ev e denv of
                           B b -> if b then ev e0 denv else ev e1 denv
\end{code}

With |ev'| fully defined, the authors define |Id|, |LVS| and |LV| to be
instances of |ComonadEv| by defining |ev| for each structure.
Basically, |ev| is |ev'| with additions sequencing and stream.

Evaluating an expression using |Id| comonad is simply the application
of |ev'| to the expression.  The instance definition could as easily
be |ev = ev'| as the definition provided.  This provides one shot
evaluation that cannot involve |Fby| or |Next| as they are not defined
for the |ev| instance for |Id|.

%% None of the examples following can be evaluated using evMainI as
%% they all involve Fby

\begin{code}
instance ComonadEv Id where
    ev e denv = ev' e denv
\end{code}

The |LV| interpreter adds |Fby| to the language interpreted by |ev'|
allowing sequencing of calculations.  Evaluating anything but an |Fby|
expression is simply calling |ev'|.  Evaluating |e0 `Fby` e1| uses
|fbyLV| to provide semantics for |Fby|.

\begin{code}
instance ComonadEv LV where
    ev (e0 `Fby` e1) denv = ev e0 denv `fbyLV` cobind (ev e1) denv
    ev e             denv = ev' e denv
\end{code}

The |LV| interpreter adds |Fby| and |Next| to the language interpreted
by |ev'| allowing sequencing of calculations.  Evaluating anything but
an |Fby| or |Next| expression is simply calling |ev'|.  Evaluating |e0
`Fby` e1| uses |fbyLVS| to provide semantics for |Fby| in the same
manner as |LV|.  Evaluating |Next e| uses |nextLVS| to provide
semantics for |Next|.

\begin{code}
instance ComonadEv LVS where
    ev (e0 `Fby` e1) denv = ev e0 denv `fbyLVS` cobind (ev e1) denv
    ev (Next e)      denv = nextLVS (cobind (ev e) denv)
    ev e             denv = ev' e denv
\end{code}

We have three interpteters that evaluate a base language.  The |Id|
monad interpreter handles basic expression evaluation, but cannot deal
with the followed by or next operations.  The |LV| monad interpreter
adds |Fby| to the language while |LVS| adds followed by and next.
However, the core language remains the same.  Thus, we can drop any
interpreter we want into this comonadic structure.  This has
implications on what compiling to a comonadic structure might result in.

Following are a vew utility functions that will prove handy when we
start evaluating language elements.  |emptyL i| produces a list of |i|
empty environments.  Similarly, |emptyS| produces a stream of
infinitely many empty environments.

\begin{code}
emptyL :: Int -> List [(a, b)]
emptyL 0 = Nil
emptyL (i + 1) = emptyL i :> []

emptyS :: Stream [(a, b)]
emptyS = [] :< emptyS
\end{code}

The |evMainI|, |evMainLVS| and |evMainLV| functions are signatures for
evaluators written for |Id|, |LVS|, and |LV| comonads respectively.
In each case, the value (|counit|) of the comonad is the current
environment.  Thus, the past and future are a |List| and |Stream| of
environments respectively.  When |evMainLVS| is called on some
expression |e| and count |i|, |ev| is initialized with a list of |i|
empty evironments, a current empty environment, and an infinite stream
of empty environments.  Both |evMainI| and |evMainLV| simply skip the
initialization of elements they do not use.

In each case, the |evMain| functions will use the comonadic evaluator
to find the $i_{th}$ environment in the past environment sequence.
(For |Id|, $i=0$ because there is no past.)  So, they generate |i|
empty environments and an empty current environment.

\begin{code}
evMainI :: Tm -> Val Id
evMainI e = ev e (Id [])

evMainLVS :: Tm -> Int -> Val LVS
evMainLVS e i = ev e (emptyL i := [] :! emptyS)

evMainLV :: Tm -> Int -> Val LV
evMainLV e i = ev e (emptyL i := [])
\end{code}

Alternatively, we can use |ev| and run functions to generate and
return lists of history elements.  In the following two examples, |ev|
is used to generate a stream transformer from a term.  |ev| is not
provided with the input comonad, the input stream must provide it.
|runLV| and |runLVS| apply that stream transformer to an empty stream
of environments.  |takeS| then takes the first several, in this case
5, elements of the output stream.  If we wanted to process input from
the stream, data can be passed to the transformer by using a stream
other than |emptyS|.

\begin{spec}
takeS 5 (runLVS (ev (sum :@ (N 1))) emptyS)
takeS 5 (runLV (ev (sum :@ (N 1))) emptyS)
\end{spec}

\begin{spec}
runLV (ev (EssenceDF.sum :@ (N 1))) emptyS
takeS 5 (runLV (ev (EssenceDF.sum :@ (N 1))) emptyS)
\end{spec}

Let's run through a collection of basic examples.  First, let's look at a variable-free term that adds two numerical values together:

\begin{code}
constSum = ((N 1) :+ (N 2))
\end{code}

Running |evMainI constSum|, |evMainLV constSum k| and |evMainLVS
constSum k| all result in |3| for any value of |k|.  The reason is the
expression does not depend on the input stream.  Thus, no matter what
the stream position is, the expression is always |3|.

Now define a simple increment function:

\begin{code}
inc = (L "x" ((V "x") :+ (N 1)))
\end{code}

and evaluate its application to |1|:

\begin{spec}
evMainI (inc :@ (N 1))
\end{spec}

Again, the value does not depend on an input stream and is constant in
any state.  Therefore, evaluation with respect to any of the comonads
will result in the same value in any context.

Now let's look at a simple application of |Fby| to see what it does.
|Fby| is not defined for the |Id| comonad.  It's |ev| function does
not define a case for it.  As there is no past or future in |Id|, the
concept of `followed by' has no meaning.

|Fby| is defined for both |LV| and |LVS| and means roughly the same
thing in both.  |x `Fby` y| takes the value |x| and is |y| thereafter.
In some senses it is a unit delay or the insertion of a value.  To
understand what is going on, consider the following evaluation:

\begin{spec}
takeS 5 (runLV (ev ((N 0 `Fby` N 1))) emptyS)
\end{spec}

The result of |runLV| is a stream whose first value is |0| and |1|
thereafter.  Nesting |Fby| instances allows creating streams of
arbitrary value orderings.  Next, let's nest the |Fby| in an
expression:

\begin{spec}
takeS 5 (runLV (ev ((N 1) :- (N 0 `Fby` N 1))) emptyS)
\end{spec}

The value of this expression is |1| minus the crrent value of |(N 0)
`Fby` (N 1)|.  We saw before that the followed by expression takes the
value of |0| followed by |1| thereafter.  Thus, this expression
evaluates to a stream of |1| followed by |0| thereafter.

|diff| defines a function that uses the |Fby| operator over a
variable.  Specifically, the value |1| used in the previous example is
abstracted out and replaced with the variable |"x"|.  When the
function is applied to a value, |"x"| is replaced with the value in
all future environments.  Thus, the value of |diff (N 1)| is |1-0|
followed by |1-1| or |1| followed by |0| thereafter.

\begin{code}
-- diff x = x - (0 `fby` x)
diff = L "x" (V "x" :- (N 0 `Fby` V "x"))
\end{code}

Evaluating |diff| on a particular number argument will result in a
sequence whose first value is the input parameter and whose subsequent
values are all |0|.  |"x"| is replace when the function is evaluated,
|x-x| will be |0| after the first sequence input.

The |pos| function is a simple stream processor that generates a value
stream of the current stream position.  The first position is 0, the
second 1, and so forth.  Accessing the $n^{th}$ element from the past
effectively returns |n|. However, for the first time the |Rec|
constructor is used to define a recursive function.

|Fby| is use to insert |0| as the first element of the stream and |pos
+ 1| thereafter where |pos| is the formal parameter to the lambda
expression.  Looking at |ev' (Rec e)| reveals that the recursion is an
standard fixed point evaluation.  Specifically, |e| must evaluate to a
function value, |F f|, reducing |Rec e| to |Rec (F f)|.  Now |Rec (F
f)| evaluates to |f (cobind (Rec (F f)) denv| giving us the the
recursive call.

One thing to observe is that in typical fixed point evaluation, the
expansion of |Rec F| is guarded by a condition that will cause the
recursion to terminate when the base case is reached.  That is not the
situation here - the expansion is not guarded and always occurs.  This
is not a problem because stream processing does not terminate.  

\begin{code}
-- pos = 0 `fby` (pos + 1)
pos = Rec (L "pos" (N 0 `Fby` (V "pos" :+ N 1)))
\end{code}

\begin{code}
-- sum x = sumx
--     where sumx = x + (0 `fby` sumx)
-- Adds a value to a running sum
sum = L "x" (Rec (L "sumx" (V "x" :+ (N 0 `Fby` V "sumx"))))

-- ini x = inix
--     where inix = x `fby` inix
-- Generates a stream of initial values
ini = L "x" (Rec (L "inix" (V "x" `Fby` V "inix")))

-- fact = 1 `fby` (fact * (pos + 1))
-- Generates a stream of factorial values.  Choosing the nth one
-- gets you n!
fact = Rec (L "fact" (N 1 `Fby` (V "fact" :* (pos :+ N 1))))

-- fibo = 0 `fby` (fibo + (1 `fby` fibo))
-- Generates a stream of fibonacci values.  Choosing the nth one
-- gets you fib(n)
fibo = Rec (L "fibo" (N 0 `Fby` (V "fibo" :+ (N 1 `Fby` V "fibo"))))

\end{code}

\begin{code}
wvr = Rec (L "wvr" (L "x" (L "y" (
                                  If (ini :@ (V "y"))
                                     (V "x" `Fby` (V "wvr" :@ (Next (V "x")) :@ (Next (V "y"))))
                                     ((V "wvr" :@ (Next (V "x"))) :@ (Next (V "y")))
                                 ))))

sieve = Rec (L "sieve" (L "x" (
                               (V "x" `Fby` (
                                             V "sieve" :@ ((wvr :@ V "x") :@ (
                                                                              V "x" `Mod` (ini :@ (V "x")) :/= N 0
                                                                                ))
                                               ))
                               )))

eratosthenes = sieve :@ (pos :+ N 2)
\end{code}

The following code block is spec'ed and not loaded.

\begin{spec}
regsel le clr a = if le && clr
                     then -1
                     else if le && |clr
                             then a
                             else if |le && clr
                                  then 0
                                  else -2

reg le clr a = (regsel le clr a) `Fby` (reg le clr a)

regsel = L "le" (L "clr" (L "a" (L "last"
                                 (If ((V "le") :&& (V "clr"))
                                     (N (-1))
                                     (If ((V "le") :&& (Not (V "clr")))
                                         (V "a")
                                         (If ((Not (V "le")) :&& (V "clr"))
                                                 (N 0)
                                                 (V "last")
                                                 )
                                     )
                                  )
                                )))

reg = Rec (L "reg" (L "le" (L "clr" (L "a" 
                                           ((((regsel :@ V "le") :@ V "clr") :@ V "a") :@ ((N (-2))
                                                                                           `Fby` 
                                                                                           ((((V "reg") :@ V "le") :@ V "clr") :@ V "a")
                                                                                           )
                                           )
                                    ))))
\end{spec}

\begin{code}

reg = L "le" (L "clr" (L "a" (Rec (L "loop"
                                         (If ((V "le") :&& (V "clr"))
                                                 (N (-1))
                                                 (If ((V "le") :&& (Not (V "clr")))
                                                         (V "a")
                                                         (If ((Not (V "le")) :&& (V "clr"))
                                                                 (N 0)
                                                                 ((N (-2)) `Fby` (V "loop"))
                                                         )
                                                 )
                                         )
                                  ))))


-- helps generate testing streams
bitStream' _ _ [] final = final
bitStream' now current scheds@((time,val):scheds') final
    | now == time = val `Fby` (bitStream' (now + 1) val scheds' final)
    | otherwise = current `Fby` (bitStream' (now +1) current scheds final)

bitStream start scheds final = bitStream' 0 start scheds final


leTest1  = FF
clrTest1 = FF

leTest2  = FF
clrTest2 = bitStream FF [(1,TT)] FF

leTest3  = bitStream FF [(1,TT)] FF
clrTest3 = bitStream FF [(1,TT)] FF

leTest4  = bitStream FF [(3,TT)] FF
clrTest4 = bitStream FF [(1,TT)] FF

leTest5  = bitStream FF [(3,TT),(5,FF)] FF
clrTest5 = bitStream FF [(1,TT)] FF

leTest6  = bitStream FF [(3,TT),(4,FF),(5,FF)] FF
clrTest6 = bitStream FF [(1,TT)] FF

leTest7  = bitStream FF [(3,TT),(4,FF),(5,TT)] FF
clrTest7 = bitStream FF [(1,TT),(2,FF),(7,TT)] FF
\end{code}

\begin{code}

unsafeLookup k al = unJust $ Data.List.lookup k al
    where unJust (Just a) = a

\end{code}

\end{document}


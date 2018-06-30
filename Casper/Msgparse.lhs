>module Msgparse (parsemsg,fnappOrVar,cpt) where

>import Messages
>import GenParse

Parser for messages appearing in protocol descriptions.  

Produced using Simon Ambler's generic parser.

type VarName = String
type Key = VarName
data Msg = Atom VarName | Encrypt Key [Msg] | Sq [Msg] | 
           Undecryptable Key [Msg] VarName | Forward VarName Key [Msg]

>msg, cpt, term, atom, variable, encryption, parenthesized :: Parse Char Msg

messages are comma-separated lists of components
msg ::= cpt [, cpt]

>parsemsg = msg

>msg = cpt ^^^ many (tokenws ',' ^^^ cpt) >>> mkcat
> where mkcat (t,[])  = t
>       mkcat (t,cts) = mkSq (t:map snd cts)

Flatten nested sequences

>mkSq ms = Sq (concat [unSeq m | m <- ms])
> where unSeq (Sq ms') = ms'
>       unSeq m' = [m']

components are either terms or %-constructs
cpt ::= term % variable | variable % term | term

>cpt = variable ^^^ tokenws '%' ^^> term >>> mkForwd
>      ||| term ^^^ tokenws '%' ^^> variable >>> mkUndec
>      ||| term
> where mkUndec (m, Atom v) = Undec m v
>       mkForwd (Atom v, m) = Forwd v m


The above means that v % v' gets interpreted as a forwarded component;
I'm not sure if that's what we want!


terms are bit-wise exclusive-ors of an atom and a term, or atoms
term ::= atom (+) term | atom

>term = atom ^^^ ws (token '(' ^^^ token '+' ^^^ token ')') ^^> term >>> mkxor
>       ||| atom
> where mkxor (m,m') = Xor m m'

atoms are function applications, variables, encryptions or parenthesized
messages

>atom = fnappOrVarOrHash ||| encryption ||| parenthesized

>fnappOrVarOrHash = 
>  optional variable parenthesized (\ (Atom f, m) -> Apply f m)


fnapp ||| variable

function applications

fnapp = 
  word ^^^ tokenws '(' ^^> msg <^^ tokenws ')'
  >>>
  (\ (f, m) -> Apply f m)

variables

>variable = word >>> Atom 


encrypted components, of the form {...}{...}
Edit to deal with non-atomic keys

>encryption = tokenws '{' ^^> msg ^^^ tokenws '}' 
>             ^^> tokenws '{' ^^> cpt <^^ tokenws '}'
>             >>> mkenc
> where mkenc (Sq ms,k) = Encrypt k ms
>       mkenc (m,k) = Encrypt k [m]

parenthesized messages

>parenthesized = tokenws '(' ^^> msg <^^ tokenws ')'

>fnappOrVar = optional variable parenthesizedAtoms mkFnApp

>mkFnApp (Atom f, [m]) = Apply f m
>mkFnApp (Atom f, ms) = Apply f (Sq ms)
 

>parenthesizedAtoms = 
>  tokenws '(' ^^> variable ^^^ many (tokenws ',' ^^> variable) <^^ tokenws ')'
>  >>> cons

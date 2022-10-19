import Pauline.Syntax
import Pauline.Statics
import Pauline.Dynamics

namespace Pauline.Notation



/-! # Atomic parsers -/

declare_syntax_cat sml_vid
syntax ident : sml_vid

syntax "[sml_vid|" sml_vid "]" : term
macro_rules
| `([sml_vid| $id:ident ]) =>
  return Lean.Syntax.mkStrLit id.getId.toString

-- Special constants
declare_syntax_cat sml_scon

syntax num : sml_scon
syntax str : sml_scon

syntax "[sml_scon|" sml_scon "]" : term
macro_rules
| `([sml_scon| $n:num ]) => `(SCon.int $n)
| `([sml_scon| $s:str ]) => `(SCon.str $s)



/-! # Types -/

declare_syntax_cat sml_typ

syntax "int" : sml_typ
syntax sml_vid : sml_typ
syntax:40 sml_typ:41 "->" sml_typ:40 : sml_typ
syntax:60 sml_typ:61 "*" sml_typ:60 : sml_typ
syntax "(" sml_typ ")" : sml_typ

syntax "[sml_typ|" sml_typ "]" : term
syntax "[sml_prodtyp|" sml_typ "]" : term

macro_rules
| `([sml_typ| int ])         => `(Typ.int)
| `([sml_typ| $id:sml_vid ]) => `(Typ.tycon [sml_vid| $id ] [])
| `([sml_typ| $t1:sml_typ -> $t2:sml_typ]) => `(Typ.arr [sml_typ| $t1] [sml_typ| $t2])
| `([sml_typ| $t1:sml_typ * $t2:sml_typ ]) => `(Typ.prod [sml_prodtyp| $t1 * $t2 ])

macro_rules
| `([sml_prodtyp| $t1:sml_typ * $t2:sml_typ * $t3:sml_typ]) =>
    `([sml_typ| $t1] :: [sml_prodtyp| $t2 * $t3]) 
| `([sml_prodtyp| $t1:sml_typ * $t2:sml_typ ]) =>
    `([[sml_typ| $t1], [sml_typ| $t2]])


/-! # Patterns -/

-- Atomic patterns
declare_syntax_cat sml_atpat
declare_syntax_cat sml_pat

syntax "_"                : sml_atpat
syntax sml_scon           : sml_atpat
syntax sml_vid             : sml_atpat
syntax "(" ")"            : sml_atpat
syntax "(" sml_pat "," sml_pat,+ ")"  : sml_atpat
syntax "[" sml_pat,+ "]"  : sml_atpat
syntax "(" sml_pat ")"    : sml_atpat

syntax sml_atpat            : sml_pat
syntax sml_vid sml_atpat     : sml_pat
syntax sml_pat ":" sml_typ  : sml_pat
--syntax sml_vid ":" sml_typ " as " sml_pat : sml_pat

syntax "[sml_pat_tuple|" sml_pat,+ "]" : term
syntax "[sml_atpat|" sml_atpat "]" : term
syntax "[sml_pat|" sml_pat "]" : term

macro_rules
| `([sml_pat_tuple| $p, $ps,*]) => `([sml_pat| $p ] :: [sml_pat_tuple| $ps,* ])
| `([sml_pat_tuple| $p ])       => `([[sml_pat| $p ]])

macro_rules
| `([sml_atpat| _              ]) => `(Pat.wild)
| `([sml_atpat| $id:sml_vid     ]) => `(Pat.bind [sml_vid| $id ])
| `([sml_atpat| ()             ]) => `(Pat.unit)
| `([sml_atpat| ( $p, $ps,* )  ]) =>
  `(Pat.tuple [sml_pat_tuple| $p, $ps,* ])
| `([sml_atpat| ($p)           ]) => `([sml_pat| $p ])

macro_rules
| `([sml_pat| $p:sml_atpat ]) => `([sml_atpat| $p ])
| `([sml_pat| $p : $t ]) => `(Pat.typed [sml_pat| $p ] [sml_typ| $t ])


syntax "[sml_atpats|" sml_atpat,* "]" : term
macro_rules
| `([sml_atpats|             ]) => `([])
| `([sml_atpats| $p          ]) => `([[sml_atpat| $p ]])
| `([sml_atpats| $p , $ps,*  ]) => `([sml_atpat| $p ] :: [sml_atpats| $ps,* ])



/-! # Expressions -/

declare_syntax_cat sml_exp

syntax sml_vid : sml_exp
syntax sml_scon : sml_exp

syntax "(" sml_exp,+ ")" : sml_exp
syntax sml_exp sml_exp : sml_exp
syntax "if " sml_exp " then " sml_exp " else " sml_exp : sml_exp
syntax "fn " sml_pat "=>" sml_exp : sml_exp

syntax sml_exp "<" sml_exp : sml_exp
syntax sml_exp "+" sml_exp : sml_exp
syntax sml_exp "-" sml_exp : sml_exp
syntax "↑" term:max : sml_exp

syntax "[sml_exp_tuple|" sml_exp,+ "]" : term
syntax "[sml_exp|" sml_exp "]" : term

macro_rules
| `([sml_exp_tuple| $e, $es,* ]) =>
  `([sml_exp| $e ] :: [sml_exp_tuple| $es,* ])
| `([sml_exp_tuple| $e:sml_exp ]) =>
  `([[sml_exp| $e ]])

macro_rules
| `([sml_exp| $id:sml_vid ]) => `(Exp.var [sml_vid| $id ])
| `([sml_exp| $sc:sml_scon ]) => `(Exp.scon [sml_scon| $sc ])
| `([sml_exp| ($e:sml_exp) ]) => `([sml_exp| $e ])
| `([sml_exp| ($e, $es,*) ]) => `(Exp.tuple [sml_exp_tuple| $e, $es,* ])
| `([sml_exp| $e1 $e2 ]) => `(Exp.app [sml_exp| $e1 ] [sml_exp| $e2 ])

| `([sml_exp| if $b then $t else $f ]) =>
  `(Exp.ite [sml_exp| $b ] [sml_exp| $t ] [sml_exp| $f ])
| `([sml_exp| fn $p => $e ]) =>
  `(Exp.lam [sml_pat| $p ] [sml_exp| $e ])

| `([sml_exp| $e1 < $e2 ]) =>
  `(Exp.app (Exp.var "<") (Exp.tuple [[sml_exp| $e1], [sml_exp| $e2 ]]))
| `([sml_exp| $e1 + $e2 ]) =>
  `(Exp.app (Exp.var "+") (Exp.tuple [[sml_exp| $e1], [sml_exp| $e2 ]]))
| `([sml_exp| $e1 - $e2 ]) =>
  `(Exp.app (Exp.var "-") (Exp.tuple [[sml_exp| $e1], [sml_exp| $e2 ]]))

| `([sml_exp| ↑$e:term ]) => `(↑$e)



/-! # Declarations -/

declare_syntax_cat sml_decl

syntax "fun" sml_vid sml_atpat+ (":" sml_typ)? "=" sml_exp : sml_decl
syntax "val" sml_pat "=" sml_exp : sml_decl
syntax "val" "rec" sml_pat "=" "fn" sml_pat "=>" sml_exp : sml_decl

syntax "[sml_decl|" sml_decl "]" : term

macro_rules
| `([sml_decl| fun $id:sml_vid $p:sml_atpat $ps:sml_atpat* = $e ]) =>
  ``(Dec.fun
      ([sml_vid| $id ])
      (⟨[sml_atpat| $p ], [sml_atpats| $ps,* ]⟩)
      none
      ([sml_exp| $e ]))
| `([sml_decl| fun $id:sml_vid $p:sml_atpat $ps:sml_atpat* : $t = $e ]) =>
  ``(Dec.fun
      ([sml_vid| $id ])
      (⟨[sml_atpat| $p ], [sml_atpats| $ps,* ]⟩)
      (some [sml_typ| $t ])
      ([sml_exp| $e ]))
| `([sml_decl| val $p = $e ]) =>
  ``(Dec.val [sml_pat| $p ] [sml_exp| $e] )
| `([sml_decl| val rec $p = fn $p2 => $e ]) =>
  ``(Dec.valrec [sml_pat| $p] [sml_pat| $p2] [sml_exp| $e] )

syntax "[sml_decls|" sml_decl,* "]" : term
macro_rules
| `([sml_decls| ])                     => `([ ])
| `([sml_decls| $d:sml_decl ])         => `([[sml_decl| $d ]])
| `([sml_decls| $d:sml_decl , $ds,* ]) => `([sml_decl| $d ] :: [sml_decls| $ds,* ])



/-! # Top level parsers -/

macro "[sml|" ds:sml_decl* "]" : term =>
  ``(Prog.mk [sml_decls| $ds,* ])

macro "[smlprop|" C:term "⊢" e:sml_exp " : " t:sml_typ "]" : term =>
  ``(HasType $C [sml_exp| $e ] [sml_typ| $t ] )

macro s:term " ==> " s':term : term =>
  ``(StepExp $s $s')

macro s:term " ==>* " s':term : term =>
  ``(StepsExp $s $s')

macro "[smlprop|" C:term "⊢" e:sml_exp " ==> " C':term "⊢" e':sml_exp "]" : term =>
  ``(StepExp ($C, [sml_exp| $e ]) ($C', [sml_exp| $e' ]))

macro "[smlprop|" C:term "⊢" e:sml_exp " ==>* " C':term "⊢" e':sml_exp "]" : term =>
  ``(StepsExp ($C, [sml_exp| $e ]) ($C', [sml_exp| $e' ]))

/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataBoole.MetaVerifier

open Strata

/--
  lowers to `r:= if(isSome(o)) then get(o) * get(o) else 0;`
-/
private def match_expr_sugar :=
#strata
program Boole;
procedure match_expr_sugar (o : option int) returns(r : int)
spec{
  ensures r >= 0;
}
{
  r := match o {
    some(a : int) => a * a,
    none => 0
  };
};


datatype Triple (a : Type, b : Type, c : Type) {
  MkTriple(fst : a, snd : b, thd : c)
};

procedure match_expr_exhaustiveness (t : Triple int int (option int)) returns(r : int)
spec{
  ensures r >= 0;
}
{
  r := match t {
    MkTriple(a : int, _, _) => a * a
  };
};

// // currently not recognized as exhaustive
// procedure exhaustiveness_gap(t : Triple int int (option int)) returns(r : int)
// spec{
//  ensures r >= 0;
// }
// {
//   r := match t {
//     MkTriple(_, _, some(v : int)) => v * v,
//     MkTriple(_, _, none) => 1
//   };
// };

#end
#eval Strata.Boole.verify "cvc5" match_expr_sugar (options := .quiet)

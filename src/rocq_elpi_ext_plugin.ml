module API = Elpi.API

open Gcd
open API
open ContextualConversion

let rat_ = AlgebraicData.declare {
  ty = TyName "ratT";
  doc = "a type of rational numbers viewed as pairs of int values";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("rat","numerator then denumerator",
      A(BuiltInData.int,A (BuiltInData.int, N)),
      B (fun n d -> { num = n; den = d }),
      M (fun ~ok ~ko t -> match t with { num = n; den = d } -> ok n d ))]
} |> (!<)

let poly_ = API.AlgebraicData.declare {
  ty = TyName "polyT";
  doc = "A type of ring expressions, simply with numeric constants," ^
        " variables, addition, and multiplication";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("pcst","constant polynomial", A(rat_, N),
      B (fun n -> Const n),
      M (fun ~ok ~ko t -> match t with Const r -> ok r | _ -> ko ()));
    K("var","indexed variable",A (BuiltInData.int, N),
      B (fun n -> Var n),
      M (fun ~ok ~ko t -> match t with Var n -> ok n | _ -> ko ()));
    K("add","binary addition",S(S(N)),
      B (fun x y -> Add (x, y)),
      M (fun ~ok ~ko t -> match t with Add (x,y) -> ok x y | _ -> ko ()));
    K("mul","binary multiplication",S(S(N)),
      B (fun x y -> Mul (x, y)),
      M (fun ~ok ~ko t -> match t with Mul (x,y) -> ok x y | _ -> ko ())); 
      ]
} |> API.ContextualConversion.(!<)

let gcd_poly_api = API.BuiltIn.MLCode(Pred ("gcd_poly",
    In(poly_, "poly1",
    In(poly_, "poly2",
    Out(poly_, "gcd",
    Out (poly_, "poly1_div",
    Out (poly_, "poly2_div",
    Easy("gcd is the greatest common divisor of poly1 and poly2," ^ 
         " poly1_div is poly1/gcd," ^
         " poly2_div is poly2/gcd")))))),
    fun (a : poly) (b : poly) _ _ _ ~depth -> 
      let result_tuple : poly * poly * poly = Gcd.poly_gcd a b in
      (match result_tuple with
        (v1, v2, v3) -> (((), Some v1), Some v2), Some v3)),
    DocAbove)

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData rat_;
  MLData poly_;
  gcd_poly_api;
]

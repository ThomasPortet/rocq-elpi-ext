open Gcd
module API = Elpi.API
module E = API.RawData

let declare = let open API.AlgebraicData in declare



let gRat = E.Constants.declare_global_symbol "rat"
let gConst = E.Constants.declare_global_symbol "gconst"
let gVar = E.Constants.declare_global_symbol "var"
let gAdd = E.Constants.declare_global_symbol "add"
let gMul = E.Constants.declare_global_symbol "mul"

let embed_rat = function
  | { num = n; den = d } -> E.mkApp gRat (API.RawOpaqueData.of_int n) [API.RawOpaqueData.of_int d]


let rat_ = API.(AlgebraicData.declare {
  ty = TyName "ratT";
  doc = "a type of rational numbers viewed as pairs of int values";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("rat","",A(BuiltInData.int,A (BuiltInData.int, N)),
      B (fun n d -> { num = n; den = d }),
      M (fun ~ok ~ko t -> match t with { num = n; den = d } -> ok n d ))]
} |> ContextualConversion.(!<))

let compute_rat_api = API.BuiltIn.MLCode(Pred("compute",
    In(rat_, "rat",
    Out(rat_, "rat",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some ( {num = 2*a.num; den = a.den})),
    DocAbove)

let poly_ = API.(AlgebraicData.declare {
  ty = TyName "polyT";
  doc = "A type of ring expressions, obtained simply with addition, multiplication, variables, and integer constants";
  pp = (fun fmt _ -> Format.fprintf fmt "<todo>");
  constructors = [
    K("gconst","",A(rat_, N),
      B (fun n -> Const n),
      M (fun ~ok ~ko t -> match t with Const r -> ok r | _ -> ko ()));
    K("var","",A (BuiltInData.int, N),
      B (fun n -> Var n),
      M (fun ~ok ~ko t -> match t with Var n -> ok n | _ -> ko ()));
    K("add","",S(S(N)),
      B (fun x y -> Add (x, y)),
      M (fun ~ok ~ko t -> match t with Add (x,y) -> ok x y | _ -> ko ()));
    K("mul","",S(S(N)),
      B (fun x y -> Mul (x, y)),
      M (fun ~ok ~ko t -> match t with Mul (x,y) -> ok x y | _ -> ko ())); 
      ]
} |> ContextualConversion.(!<))


let compute_poly_api = API.BuiltIn.MLCode(Pred("compute_poly",
    In(poly_, "poly",
    Out(poly_, "poly",
    Easy("AAA"))),
    fun a _ ~depth -> (), Some ( a)),
    DocAbove)
let gcd_poly_api = API.BuiltIn.MLCode(Pred ("gcd_poly",
    In(poly_, "poly1",
    In(poly_, "poly2",
    Out(poly_, "gcd",
    Easy("AAA")))),
    fun a (b : poly) _ ~depth -> (), Some ( poly_gcd a b)),
    DocAbove)
let factorize_poly_api = API.BuiltIn.MLCode(Pred ("factorize_poly",
    In(poly_, "poly1",
    In(poly_, "poly2",
    Out(poly_, "poly1",
    Out(poly_, "poly2",
    Easy("AAA"))))),
    fun (a:poly) (b : poly) _ _ ~depth -> ((), Some(fst (factorize a b))), Some (snd (factorize a b))),
    DocAbove)

let builtins =
  API.BuiltIn.declare ~file_name:"ext.elpi" [
  MLData rat_;
  MLData poly_;
  compute_rat_api;
  compute_poly_api;
  gcd_poly_api;
  factorize_poly_api
]

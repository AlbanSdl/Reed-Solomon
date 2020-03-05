(** Le code a été réalisé pour un TP à partir du sujet de 
  * composition d'informatique de Polytechnique de l'année 2007 *)

let p = 1523;;

let rec euclide a b =
    if b == 0 then 1, 0, a
    else let up, vp, d = euclide b (a mod b) in vp, (up - a/b * vp), d;;

(* Retourne l'inverse de l'entier dans Z/pZ *)
let inv x = match euclide (x mod p) p with
    b,_,_ -> b mod p;;

type poly = int list;;

(* Renvoie le polynome évalué en x *)
let rec valeur poly x = match poly with
    t::q -> (t + x * valeur q x) mod p
  | [] -> 0;;

(* Codage *)
let rec codage coefs poly = match coefs with
    t::q -> ((valeur poly t) mod p)::codage q poly
  | [] -> [];;

(* Additionne deux polynomes*)
let rec addition poly1 poly2 = match poly1, poly2 with
    t::q, u::v -> ((t + u) mod p)::addition q v
  | [], u::v -> (u mod p)::addition [] v
  | t::q, [] -> (t mod p)::addition q []
  | [], [] ->  [];;

(* Soustrait deux polynomes *)
let rec soustraction poly1 poly2 = match poly1, poly2 with
    t::q, u::v -> ((t - u) mod p)::soustraction q v
  | [], u::v -> ((-u) mod p)::soustraction [] v
  | t::q, [] -> (t mod p)::soustraction q []
  | [], [] ->  [];;

(* Réalise le produit du polynome par un scalaire *)
let rec produitParScalaire poly s = match poly with
    t::q -> ((t*s) mod p)::produitParScalaire q s
  | [] ->  [];;

(* Réalise le produit de deux polynomes *)
let produit poly1 poly2 = let coefs = ref [||] in let coef = ref 0 in let a = ref 0 in let b = ref 0 in
    for k = 0 to Array.length (Array.of_list poly1) + Array.length (Array.of_list poly2) - 2 do 
        for j = 0 to k do
            if Array.length (Array.of_list poly2) > k - j then a := (Array.of_list poly2).(k-j) else a := 0;
            if Array.length (Array.of_list poly1) > j then b := (Array.of_list poly1).(j) else b := 0;
            coef := !coef + !a * !b;
        done;
        coefs := Array.append !coefs [|!coef mod p|];
        coef := 0;
    done;
    Array.to_list !coefs;;

(* Permet d'obtenir le degré d'un polynome
 * On établit que dans le programme, un degré infini correspond à -1 *)
let degre poly = let polyArray = ref (Array.of_list poly) in let degre = ref (-1) in let pending = ref 0 in for k = 0 to Array.length !polyArray - 1 do
    pending := !pending + 1;
    if !polyArray.(k) != 0 then (degre := !degre + !pending; pending := 0)
  done;
  !degre;;

(* Permet d'obtenir le coefficient dominant *)
let coeffDominant poly = (Array.of_list poly).(degre poly);;
(* Multiplie le polynome par X^n *)
let shiftCoefs poly n = Array.to_list (Array.append (Array.make n 0) (Array.of_list poly));;

(* Effectue la division euclidienne d'un polynome par un autre *)
let division poly1 poly2 = let poly1 = ref poly1 in let quotient = ref (Array.make (degre !poly1 - degre poly2 + 1) 0) in while degre !poly1 >= degre poly2 do 
    !quotient.(degre !poly1 - degre poly2)<-(!quotient.(degre !poly1 - degre poly2) + coeffDominant !poly1 / coeffDominant poly2);
    poly1 := soustraction !poly1 (shiftCoefs (produitParScalaire poly2 (coeffDominant !poly1 / coeffDominant poly2)) (degre !poly1 - degre poly2));
  done;
  Array.to_list !quotient, !poly1;;

(* Renvoie le reste de la d.e. de poly1 par poly2
 * Note: cette fonction appelle directement `division` et a donc la même complexité.
 * Si vous voulez également utiliser le quotient de la division euclidienne il est
 * donc préférable d'appeler `division` *)
let modulo poly1 poly2 = let _,a = division poly1 poly2 in a;;


(* PARTIE III DU PROBLEME : MULTIPLICATION ET DIVISION RAPIDE *)
let subList list indexFrom indexTo = Array.to_list(Array.sub (Array.of_list list) indexFrom (indexTo - indexFrom));;

(* Cette fonction calcule le produit de polynomes avec une complexité en O(l^log2(3)), en utilisant
 * une décomposition des polynomes en U(X) = Ub + X^e * Uh (et effectue une sorte de produit par dichotomie) *)
let rec produitRapide poly1 poly2 = let e = ref ((degre poly1 + 1) / 2) in  let wb = ref [] in  let wh = ref [] in  let wm = ref [] in let produitRapideAux poly1 poly2 = if degre poly1 < 2 then produit poly1 poly2 else produitRapide poly1 poly2 in
  let ub = subList poly1 0 !e in  let uh = subList poly1 !e (degre poly1 + 1) in  let vb = subList poly2 0 !e in let vh = subList poly2 !e (degre poly2 + 1) in
  wb := produitRapideAux ub vb;
  wh := produitRapideAux uh vh;
  wm := soustraction (soustraction (produitRapideAux (addition uh ub) (addition vb vh)) !wh) !wb;
  addition (addition (shiftCoefs !wh (2 * !e)) (shiftCoefs !wm !e)) !wb;;

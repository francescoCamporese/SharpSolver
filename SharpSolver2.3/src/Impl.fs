(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Impl.fsi: implementazioni degli studenti
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Impl

open Absyn
open Prelude
open System
open System.Runtime.Remoting.Metadata.W3cXsd2001
open System.Numerics

let rationalize (x : float) : rational = //partendo da denominatore = 10, moltiplico x e denominatore finchè la parte non intera di x non diventa 0
    if x = 0.0 then //caso x = 0: numeratore e denominatore saranno 0
        rational (0 , 0)
    else if x % (float(int (x))) = 0.0 then //se x ha come parte decimale 0 teoricamente è un intero: restituisco n = |x| e d = 1
        rational (int(x) , 1)
    else
        let mutable y = x
        let mutable n = 0 
        let mutable d = 1
        while (y % (float(int (y)))) <> 0.0 do //finchè ho qualcosa dopo la virgola, diverso da 0, moltiplico per 10
            y <- y * 10.0
            n <- int(y)
            d <- d * 10
        rational (n , d)
                                            

let monomial_degree (m : monomial) : int = //so che un monomial contiene una coppia (coefficiente, grado)
    match m with
    |Monomial (coeff , deg) -> match coeff with
                               |coeff when coeff = rational 0 -> 0
                               |_ -> deg

let monomial_negate (m : monomial) : monomial = //restituisco un monomial col coefficiente di segno negato
    match m with
    |Monomial (coeff , deg) -> Monomial (-coeff , deg)

let polynomial_degree (p : polynomial) : int = //il grado di un polinomio è il grado massimo tra quelli dei suoi monomi
    let mutable maxDeg = 0
    let rec aux p = //utilizzo questa funzione per non dover rendere ricorsiva la funzione polynomial_degree 
        match p with
        |[] -> maxDeg
        |x :: xs -> match x with
                    |Monomial (coeff , deg) -> if (deg > maxDeg && coeff <> rational 0) then //il monomio ha grado massimo
                                                   maxDeg <- deg
                                                   aux xs
                                               else
                                                   aux xs
    match p with
    |(Polynomial mon_list) -> aux mon_list //richiamo aux sul contenuto del polynomial, cioè su una lista di monomial

let polynomial_negate (p : polynomial) : polynomial = //un polinomio negato è un polinomio costituito dai suoi monomi con i loro coefficienti di segno opposto
    let mutable final_list = []
    let rec auxB p =
                    match p with
                    |[] -> Polynomial final_list //restituisco un polinomio contenente la lista di monomi che ho creato
                    |x :: xs -> (final_list <- final_list @ [monomial_negate x]) //concateno alla lista i monomi negati
                                auxB xs
    match p with
    |(Polynomial mon_list) -> auxB mon_list

let normalized_polynomial_degree (np : normalized_polynomial) : int =  
    match np with
    |(NormalizedPolynomial rat_arr) -> (rat_arr.Length) - 1 //(trovo la lunghezza - 1) dell' array di rational contenuto nel polinomio normalizzato perchè se è di n-esimo grado avrò n + 1 coefficienti

let normalize (p : polynomial) : normalized_polynomial = 
    let normalized_to_monomial (arr: rational []) = //restituisce una lista di monomi di tipo coefficiente*x^posizione
        let mutable list = []
        for i = 0 to (arr.Length - 1) do
            list <- list @ [Monomial (arr.[i] , i)]
        list
    let rec aux p = 
        let mutable arrCoeffs = Array.init ((polynomial_degree p) + 1) (fun _ -> rational 0) //inizializzo l' array di coefficienti di tipo rational con (grado del polinomio posizioni + 1)
        let rec auxC p =
            match p with
            |[] -> NormalizedPolynomial arrCoeffs //costruisco un polinomio normalizzato contenente l' array di coefficienti
            |x :: xs -> match x with
                        |Monomial (coeff , deg) -> ((arrCoeffs.[monomial_degree x]) <- ((arrCoeffs.[monomial_degree x]) + coeff)) //ottengo il coefficiente di ogni monomio di un certo grado e lo sommo all' elemento dell' array in posizione uguale al grado del monomio
                                                   auxC xs
        match p with
        |(Polynomial mon_list) -> auxC mon_list
    in
    match aux p with
    |(NormalizedPolynomial np) -> aux (Polynomial (normalized_to_monomial np)) //chiamo aux su un polinomio costruito attorno ad una lista di monomi creata a partire dal polinomio normalizzato costruito utilizzando normalized_to_monomial



let derive (p : polynomial) : polynomial = 
    let mutable listOfMon = [] //lista che conterrà le derivate dei monomi del polinomio dato
    let rec auxE p =
        match p with
        |[] -> Polynomial listOfMon
        |x :: xs -> match x with
                    |Monomial (coeff , deg) -> if (deg = 0 || coeff = rational 0) then //se il grado o il coefficiente sono 0 scarto il monomio altrimenti avrei zeri inutili nella stampa
                                                auxE xs
                                               else //derivata di a*x^n = n*a*x^(n - 1)
                                                listOfMon <- listOfMon @ [Monomial (((rational deg) * coeff), (deg - 1))]
                                                auxE xs
    match p with
    |(Polynomial mon_list) -> auxE mon_list

let reduce (e : expr) : polynomial = //restituisce un polinomio partendo dall' espressione
    let rec reducer e =
        match e with
        |(Poly pol) -> pol //se expr è un polinomio lo restituisco
        |(Derive der) -> derive (reducer der) //se expr è una derivata, ripeto la funzione sulla derivata
    reducer e

let solve0 (np : normalized_polynomial) : bool =                            
    match np with //il contenuto del polinomio normalizzato sarà un array di rational ma...
    |(NormalizedPolynomial rat_el) -> rat_el.[0] = rational 0 //essendo il polinomio composto da un monomio di grado 0 avrò un rational che dirò se è uguale a 0 o no

let solve1 (np : normalized_polynomial) : rational = //il risultato sarà -b/a, so che in pos. 0 ho b e in pos. 1 ho a
    match np with
    |(NormalizedPolynomial rat_el) -> (- (rat_el.[0])) / (rat_el.[1]) //avendo un array di rational basta fare il calcolo sugli elementi nelle relative posizioni
                                                                                       
let solve2 (np : normalized_polynomial) : (float * float option) option = 
    match np with //so che il polinomio è un array costituito da 3 coefficienti rational
    |NormalizedPolynomial [|c0 ; c1 ; c2|] -> let a = float c2 //converto i rational in float in modo da poter fare i calcoli
                                              let b = float c1
                                              let c = float c0
                                              let delta = (b * b) - (4.0 * a * c) //assegno il valore del delta in modo da inserirlo comodamente nelle formule
                                              match delta with //la quantità di soluzioni dipende dal delta
                                              |delta when delta > 0.0 -> let x1 = ((- b) + (sqrt delta)) / (2.0 * a) //due soluzioni reali distinte
                                                                         let x2 = ((- b) - (sqrt delta)) / (2.0 * a)
                                                                         Some (x1 , Some x2)
                                              |delta when delta = 0.0 -> let coincResult = (- b) / (2.0 * a) //due soluzioni reali coincidenti
                                                                         Some (coincResult , None)
                                              |delta when delta < 0.0 -> None //nessuna soluzione nei numeri reali




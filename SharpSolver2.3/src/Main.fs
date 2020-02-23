(*
 * SharpSolver - Progetto di Programmazione e Calcolo a.a. 2018-19
 * Main.fs: console e codice main
 * (C) 2018 Alvise Spano' @ Universita' Ca' Foscari di Venezia
 *)

module SharpSolver.Main

open Microsoft.FSharp.Text.Lexing
open Absyn
open System
open Prelude
open Microsoft.FSharp.Text
open SharpSolver
open SharpSolver


// funzioni di logging e printing
//

let hout hd fmt =
    if not <| String.IsNullOrWhiteSpace hd then
        printf "[%s]%s" hd (new String (' ', max 1 (Config.prefix_max_len - String.length hd)))
        stdout.Flush ()
    printfn fmt

let chout col hd fmt =
    let c = Console.ForegroundColor
    Console.ForegroundColor <- col
    Printf.kprintf (fun s -> hout hd "%s" s; Console.ForegroundColor <- c) fmt

let out fmt = hout "" fmt
let cout col fmt = chout col "" fmt

let norm fmt = chout ConsoleColor.Yellow "norm" fmt
let redux fmt = chout ConsoleColor.Magenta "redux" fmt
let degree fmt = chout ConsoleColor.Cyan "degree" fmt //aggiunto io perchè mancava
let sol fmt = chout ConsoleColor.Green "sol" fmt
let ident fmt = chout ConsoleColor.Green "ident" fmt    
let error fmt = chout ConsoleColor.Red "error" fmt   

// interprete dei comandi e delle espressioni
//

let interpreter_loop () =
    while true do
        printf "\n%s" Config.prompt_prefix          // stampa il prompt
        stdout.Flush ()                             // per sicurezza flusha lo stdout per vedere la stampa del prompt senza end-of-line
        let input = Console.ReadLine ()             // leggi l'input scritto dall'utente
        let lexbuf = LexBuffer<_>.FromString input  // crea un lexbuffer sulla stringa di input

        // funzione locale per il pretty-printing degli errori
        let localized_error msg =
            let tabs = new string (' ', Config.prompt_prefix.Length + lexbuf.StartPos.Column)
            let cuts = new string ('^', let n = lexbuf.EndPos.Column - lexbuf.StartPos.Column in if n > 0 then n else 1)
            cout ConsoleColor.Yellow "%s%s\n" tabs cuts
            error "error at %d-%d: %s" lexbuf.StartPos.Column lexbuf.EndPos.Column msg 
        
        // blocco con trapping delle eccezioni
        try
            let line = Parser.line Lexer.tokenize lexbuf    // invoca il parser sul lexbuffer usando il lexer come tokenizzatore
            #if DEBUG
            hout "absyn" "%+A" line
            hout "pretty" "%O" line
            #endif

            // interpreta la linea in base al valore di tipo line prodotto dal parsing
            match line with
            | Cmd "help" ->
                out "%s" Config.help_text

            | Cmd ("quit" | "exit") ->
                out "%s" Config.exit_text
                exit 0

            // TODO: se volete supportare altri comandi, fatelo qui (opzionale)
            
            | Cmd s -> error "unknown command: %s" s    // i comandi non conosciuti cadono in questo caso

            // TODO: aggiungere qui sotto i pattern per i casi Expr ed Equ con relativo codice per, rispettivamente, normalizzare espressioni e risolvere equazioni
            | Expr e1 -> 
                redux "%O" (Impl.reduce e1) //applicazione di reduce all' espressione
                norm "%O" (Impl.normalize (Impl.reduce e1)) //versione normalizzata del polinomio derivato
                degree "%O" (Impl.normalized_polynomial_degree (Impl.normalize (Impl.reduce e1))) //grado della versione normalizzata del polinomio derivato

            | Equ (e1 , e2) ->
                let leftSide = Impl.reduce e1 //monomi a sinistra dell' uguale
                let mutable rightSide = Impl.reduce e2 //variabile perchè dopo redux nego i monomi a destra dell' uguale perchè vanno spostati alla sua sinistra
                
                redux "%O = %O" leftSide rightSide //applicazione di reduce alle due espressioni
                let mutable singleNormPol = Impl.normalize (Polynomial([Monomial (rational (0) , 0)])) //inizializzo singleNormPol
                if leftSide = rightSide then //se ho un' uguaglianza che semplificata è 0 = 0
                    singleNormPol <- Impl.normalize (Polynomial([Monomial (rational (0) , 0)]))//non lo modifico
                else
                    rightSide <- Impl.polynomial_negate(rightSide)

                    let left = let unboxLs leftSide = leftSide //lista di monomi contenuti nel polinomio a sinistra dell' uguale
                               match leftSide with
                               |(Polynomial mon_list) -> unboxLs mon_list    
                    let right = let unboxRs rightSide = rightSide //lista di monomi contenuti nel polinomio a destra dell' uguale
                                match rightSide with
                                |(Polynomial mon_list) -> unboxRs mon_list
                
                    singleNormPol <- Impl.normalize (Polynomial (left @ right)) //monomi a sinistra + (- monomi a destra)
                norm "%O = 0" singleNormPol

                let singleNormPolDeg = Impl.normalized_polynomial_degree (singleNormPol) //grado del polinomio normalizzato
                degree "%O" singleNormPolDeg

                match (singleNormPolDeg) with //in base al grado, stampa la stringa contentente il risultato dell' equazione costituita dal polinomio = 0
                | 0 -> ident "%O" (Impl.solve0 singleNormPol)
                | 1 -> out "Risultato: x = %O" (Impl.solve1 singleNormPol)
                | 2 -> match (Impl.solve2 singleNormPol) with //in base alla soluzione faccio una stampa adeguata
                       |Some (x1 , x2) when x2 <> None -> sol "x1 = %O e x2 = %O" x1 x2.Value //x2.value serve ad ottenere il valore float del secondo elemento
                       |Some (x1 , x2) when x2 = None -> sol "x1 = x2 = %O" x1
                       |None -> sol "L' equazione non ha soluzioni nei numeri reali"
                | _ -> error "L' equazione non e' risolvibile perche' di grado superiore al secondo"

            | _ -> raise (NotImplementedException (sprintf "unknown command or expression: %O" line))
                   
        // gestione delle eccezioni
        with LexYacc.ParseErrorContextException ctx ->
                let ctx = ctx :?> Parsing.ParseErrorContext<Parser.token>
                localized_error (sprintf "syntax error%s" (match ctx.CurrentToken with Some t -> sprintf " at token <%O>" t | None -> ""))

           | Lexer.LexerError msg -> localized_error msg 

           | :? NotImplementedException as e -> error "%O" e
        
           | e -> localized_error e.Message


// funzione main: il programma comincia da qui
//

[<EntryPoint>]
let main _ = 
    let code =
        try
            interpreter_loop ()                 // chiama l'interprete
            0                                   // ritorna il codice di errore 0 (nessun errore) al sistema operativo se tutto è andato liscio
        with e -> error "fatal error: %O" e; 1  // in caso di eccezione esce con codice di errore 1
    #if DEBUG
    Console.ReadKey () |> ignore                // aspetta la pressione di un tasto prima di chiudere la finestra del terminare 
    #endif
    code



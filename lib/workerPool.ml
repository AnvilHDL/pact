(* A fixed set of worker domains for data-parallel maps. *)

(* Number of domains, including the caller; set by -j. *)
let jobs = ref 1

type t = {
  mutable domains : unit Domain.t list;
  mutex : Mutex.t;
  wake : Condition.t;
  idle : Condition.t;
  mutable job : unit -> unit;
  mutable generation : int;
  mutable running : int;
  mutable stop : bool;
}

let worker p =
  let seen = ref 0 in
  let rec loop () =
    Mutex.lock p.mutex;
    while p.generation = !seen && not p.stop do Condition.wait p.wake p.mutex done;
    if p.stop then Mutex.unlock p.mutex
    else begin
      seen := p.generation;
      let job = p.job in
      Mutex.unlock p.mutex;
      job ();
      Mutex.lock p.mutex;
      p.running <- p.running - 1;
      if p.running = 0 then Condition.signal p.idle;
      Mutex.unlock p.mutex;
      loop ()
    end
  in
  loop ()

let create n =
  let p = { domains = []; mutex = Mutex.create (); wake = Condition.create ();
            idle = Condition.create (); job = ignore; generation = 0; running = 0;
            stop = false } in
  let n = max 1 (min n (Domain.recommended_domain_count ())) in
  p.domains <- List.init (n - 1) (fun _ -> Domain.spawn (fun () -> worker p));
  p

let shutdown p =
  Mutex.lock p.mutex;
  p.stop <- true;
  Condition.broadcast p.wake;
  Mutex.unlock p.mutex;
  List.iter Domain.join p.domains;
  p.domains <- []

let with_pool f =
  let p = create !jobs in
  Fun.protect ~finally:(fun () -> shutdown p) (fun () -> f p)

(* Run [run] on every worker and on the caller; return when all have finished. *)
let run_all p run =
  Mutex.lock p.mutex;
  p.job <- run;
  p.generation <- p.generation + 1;
  p.running <- List.length p.domains;
  Condition.broadcast p.wake;
  Mutex.unlock p.mutex;
  run ();
  Mutex.lock p.mutex;
  while p.running > 0 do Condition.wait p.idle p.mutex done;
  p.job <- ignore;
  Mutex.unlock p.mutex

(* Map [f] over [xs]; results keep input order, and exceptions are returned, not raised. *)
let map p f xs =
  let n = Array.length xs in
  let results = Array.make n (Error Exit) in
  let apply i = results.(i) <- (try Ok (f xs.(i)) with e -> Error e) in
  if n <= 1 || p.domains = [] then
    for i = 0 to n - 1 do apply i done
  else begin
    let next = Atomic.make 0 in
    let rec go () =
      let i = Atomic.fetch_and_add next 1 in
      if i < n then (apply i; go ())
    in
    run_all p go
  end;
  results

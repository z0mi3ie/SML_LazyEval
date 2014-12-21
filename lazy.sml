
use "mergesort.sml";

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Permutation Sequence Data Type 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
datatype 'a permutationSeq = Cons of 'a option * (unit-> 'a permutationSeq )

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Name       : getStart
 | Paramaters : list of things                                                             
 | Returns    : a list with a original position list zipped on                                                             
 |                                                              
 | Takes the list passed it, zips it up with the positions, and returns it   
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun zipPosition l = ListPair.zip( (List.tabulate( (List.length l), (fn x => x ) ), l ) ) 
  
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Name       : findA
 | Paramaters : a list                                                            
 | Returns    : returns an integer index of furthest point of a < b
 |                                                               
 | The index of Ai before Ai plus 1 where Ai < Ai + 1 value wise   
 |                                                             
  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*) 
fun findA l = 
  let 
    fun loop( [], i  )                 =  i  (* ...SHOULD NEVER REACH THIS... *) 
      | loop( (aI,aD)::[], i )         =  i  (* Last perm sequence found : returns Data at first element *)
      | loop( (aI,aD)::(bI,bD)::t, i ) = if aI > bI then (i-1)                
                                                    else loop( (bI,bD)::t, i-1 )
  in
    loop( List.rev l, ( List.length l - 1 ) )
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Name       : findB
 | Paramaters : A value of a node, and the Ai+1 part of list                                                            
 | Returns    : an integer index of B                                                             
 |                                                              
 | Finds the node that is > A and < then the rest in its own list   
 |                                                             
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun findB( A_VAL, l ) =
  let
    fun loop( (A1,A2), [],         sv, si, cur ) = ( (A1,A2),[], sv, si , cur   ) (*None left*)
      | loop( (A1,A2), (H1,H2)::t, sv, si, cur ) = if H1 > A1 andalso H1 < sv then  loop( (A1,A2), t, H1, cur, cur+1 ) (*Found new index*)
                                           else loop( (A1,A2), t, sv, si , cur+1 ) (*Did not find new index*)
  in
    #4( loop( A_VAL, l, #1(hd l), 0, 0 ) )
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Name       : swap
 | Paramaters : a list, index of things to swap.                                                            
 | Returns    : a list with the swaps done to it                                                             
 |                                                              
 | Constructs a new list keeping track of index with the order swapped   
 | of things with the designated indexes. A goes to B spot and vica versa                                                            
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun swap( l, A, B, Ai, Bi ) = 
  let
    fun loop( [], _, _, _, _, INDEX, acc ) = ( List.rev acc )
      | loop( h::t, A, B, Ai, Bi, i, acc ) = if     ( i = Ai ) then loop( t, A, B, Ai, Bi, i+1, B::acc )
                                             else if( i = Bi ) then loop( t, A, B, Ai, Bi, i+1, A::acc )
                                             else                   loop( t, A, B, Ai, Bi, i+1, h::acc )
  in
    loop( l, A, B, Ai, Bi, 0, [] ) 
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Name       : splitList
 | Paramaters : a list, and the index to split on                                                            
 | Returns    : a tuple of the first half, and the second half of the list                                                             
 |                                                                  
 | Makes use of take and drop to return a tuple of a split list   
 |                                                            
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun splitList  l n    = ( List.take( l, n + 1 ), List.drop( l, n + 1 ) )
fun firstPart  l n    = List.take( l, n + 1 )
fun secondPart l n    = List.drop( l, n + 1 )

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Unzips a list of tuples into a tuple of two lists. 
 |  Using this for (INDEX,YOURVALUES) to a list of just [YOURVALUES]
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*) 
fun unzipIndexes l =
  let
    fun loop ( [], acc ) = (List.rev acc)
      | loop ((hI, hV)::t, acc ) = (loop( t, (hI::acc) ) )
  in
    loop( l, [] )
  end

fun unzipValues l =
  let
    fun loop ( [], acc ) = (List.rev acc)
      | loop ((hI, hV)::t, acc ) = ( loop( t, (hV::acc) ) )
  in
    loop(l, [])
  end
 
 (*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 |  getPermutation l 
      Given a list of (INDEX,VALUES) tuples, this will return the 
      list of the the NEXT permutation from the given list in the 
      arguments. 

      Keep in mind this list will have a type ( int * 'a ) list
      so in order to match the original types we need to unzip the
      int indexes away. 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun getPermutation [] = []
  | getPermutation [x] = [x]
  | getPermutation l = 
  let
    val AINDEX = findA l 
    val AVALUE = (List.nth( l, AINDEX ))
    val BINDEX = (findB( AVALUE, ( secondPart l (AINDEX) ) ) ) + AINDEX + 1 
    val BVALUE = (List.nth( l, BINDEX ))
    val SWAP_AB = swap( l, AVALUE, BVALUE, AINDEX, BINDEX )
    val LIST_UP_TO_B  = firstPart  SWAP_AB (AINDEX) 
    val LIST_PASSED_B = secondPart SWAP_AB (AINDEX)
    val SORTED_PAST_B = merge_sort LIST_PASSED_B
    val COMPLETE_PERMUTATION_LIST = (LIST_UP_TO_B@SORTED_PAST_B)
  in
    COMPLETE_PERMUTATION_LIST
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | isLast
    Takes a tuple list in of (Index, Value) and returns true if the perm
    sequence has more permutations or false if this list is the last
    sequence. 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun isLast l = 
  let
    val indexList = unzipIndexes l
    fun loop []        = true
      | loop (x::nil)  = true
      | loop (a::b::c) = if a < b then false
                         else loop (b::c)
  in
    loop indexList 
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Permutation l and permutation type 'constructors for various
   parts of the program 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

fun none l  = Cons( NONE,   ( fn () => none l ) )

fun perm l  = Cons( SOME (unzipValues l), ( fn () => if ( isLast l ) then none l 
                                            else perm( getPermutation l ) ) ) 

fun permutation l = perm ( zipPosition l ) 

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Next Function
   fn : 'a permutationSeq -> 'a option
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun next (Cons (NONE, func))   = NONE
  | next (Cons (SOME l, func)) = SOME l

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Rest Function
   fn : 'a permutationSeq -> 'a permutationSeq
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun rest ( Cons(SOME _, t ) ) = (t())
  | rest ( Cons(NONE, t ) )   = (t())

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Print Function
        string permutationSeq -> unit
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun printPermutations l = 
  let 
    fun printPerm strL = List.app ( fn cur => (print cur) ) strL
    fun curPermString [] = "\n" 
      | curPermString (h::t) = h^curPermString( t );
    fun stringList (Cons(NONE, f)) = []
      | stringList (Cons(SOME l, f)) = ( curPermString l)::(stringList (f()) )
    
    val PERMSTRINGLIST = stringList l
  in
    printPerm PERMSTRINGLIST
  end

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
 | Find *BONUS*
        ('a -> bool) -> 'a permutationSeq -> 'a * 'a permutationSeq
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
fun find boolFun permSeq =
  let

    fun loop bf ( Cons(NONE, func) ) = (NONE, func) 
      | loop bf ( Cons(SOME curSeq, func) ) = if ( bf curSeq ) then  ( ( SOME  curSeq  ) , (func) ) 
                                                                             else loop bf (func()) 
  in
    loop boolFun permSeq 
  end


(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
          Bench Mark Functions / Testing Functions 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*fun benchmark (Cons(NONE,f)) = []*)
(*| benchmark (Cons(SOME l, f)) = l::( benchmark (f()) )*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
          TESTS TESTS TESTS TESTS 
 ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(*val EMPTYLIST    = [] *)
(*val MEDIUMLIST    = ["a","b","c","d","e","f","g","h","i"]*)
(*val SMALLLIST     = ["0","1","2","3"]*)
(*val SMALL_PERM  = permutation SMALLLIST*)
(*;printPermutations SMALL_PERM;*)
(*val lilfun = fn (x) => if hd( x ) = "c" then true else false*)
(*val findTest = find lilfun SMALL_PERM*)
(*val t_start = Timer.startRealTimer();*)
(*val BM = benchmark ( permutation  ["a","b","c","d","e","f","g","h","i"])*)
(*val t_end = Timer.checkRealTimer t_start;*)


(*val next1 = next (SMALL_PERM)*)
(*val next2 = next( rest SMALL_PERM )*)
(*val next3 = next( rest ( rest SMALL_PERM ) )*)
(*val next4 = SMALL_PERM*)
(*val next5 = SMALL_PERM*)
(*val next6 = SMALL_PERM*)

(*
val HUGELIST = List.tabulate ( 100, (fn x => x + 1 ) )
val HUGEPERM = permutation HUGELIST
val NEXTHUGE = next HUGEPERM
val RESTHUGE = rest HUGEPERM
val BUNCHACALLS = next ( rest ( rest ( rest ( rest ( rest ( HUGEPERM ) ) ) ) ) ) 
*)
 

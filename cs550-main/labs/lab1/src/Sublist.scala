
import stainless.lang._
import stainless.collection._
import stainless.annotation._

/* 
 * The definition of List and its operations can be found here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala
 * You should not need them, but you can find some lemmas on List here:
 * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/ListSpecs.scala
 */

def sublist[T](l1: List[T], l2: List[T]): Boolean = {
  (l1, l2) match {
    case (Nil(), _)                 => true
    case (_, Nil())                 => false
    case (Cons(x, xs), Cons(y, ys)) => (x == y && sublist(xs, ys)) || sublist(l1, ys)
  }
}

@extern
@main
def main(): Unit = {
  def example(lhs: List[Int], rhs: List[Int]): Unit = {
    println(s"${lhs.toScala.mkString("<", ",", ">")} ⊑ ${rhs.toScala.mkString("<", ",", ">")} = ${sublist(lhs, rhs)}")
  }

  example(List(0, 2), List(0, 1, 2))
  example(List(0, 0, 2), List(0, 2))
  example(List(1, 0), List(0, 0, 1))
  example(List(10, 5, 25), List(70, 10, 11, 8, 5, 25, 22))
  example(List(25, 11, 53, 38), List(15, 25, 11, 8, 53, 22, 38))
}

object SublistSpecs {
 
  /* forall l, sublist(l, l) */
  def reflexivity[T](l: List[T]): Unit = {
    /* TODO: Prove me */
    l match {
      case Nil() =>
        ()
      case Cons(_,xs) =>
        reflexivity(xs)
    }
  }.ensuring(_ =>
    sublist(l, l)
  )
 
  def leftTail[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && sublist(l1, l2))
    if(sublist(l1,l2.tail)) then leftTail(l1,l2.tail)
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1.tail, l2)
  )
 
  def tails[T](l1: List[T], l2: List[T]): Unit = {
    require(!l1.isEmpty && !l2.isEmpty && l1.head == l2.head && sublist(l1, l2))

    if sublist(l1,l2.tail) then leftTail(l1,l2.tail)   
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1.tail, l2.tail)
  )
 
  /* forall l1 l2 l3, sublist(l1, l2) /\ sublist(l2, l3) ==> sublist(l1, l3) */
  def transitivity[T](l1: List[T], l2: List[T], l3: List[T]): Unit = { // find a counter example
    require(sublist(l1, l2) && sublist(l2, l3))
    (l1, l2, l3) match {
    case (Nil(), _, _) => ()
    case (Cons(x, xs), Cons(y, ys), Cons(z, zs)) =>
      if (x == y && y == z) {
        tails(l1, l2)//do cut trasformation, and same time do the ensuring of each tail
        tails(l2, l3)
        transitivity(l1.tail, l2.tail, l3.tail)
      } else  if (x != y && sublist(l1, l2.tail)) {
        leftTail(l2, l3)
        transitivity(l1, l2.tail, l3)
      } else  if (y != z && sublist(l2, l3.tail)) {
        transitivity(l1, l2, l3.tail)
      } 

  }
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1, l3)
  )
 
  def lengthHomomorphism[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x == y) {
          tails(l1, l2)
          lengthHomomorphism(l1.tail, l2.tail)
        } else {
          if(sublist(l1, l2.tail)) then lengthHomomorphism(l1, l2.tail)
        }
    }
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1.length <= l2.length  //postcondition is part of the next proof precondition
  )
 
  def biggerSublist[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && l1.length >= l2.length)
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x == y) {
          tails(l1, l2)
          biggerSublist(l1.tail, l2.tail)
        } else {
          if(sublist(l1, l2.tail)) then biggerSublist(l1, l2.tail)
        }
    }
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1 == l2
  )
 
  def antisymmetry[T](l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2) && sublist(l2, l1))
    (l1, l2) match {
      case (Nil(), Nil()) => ()
      case (Cons(x, xs), Cons(y, ys)) =>
          lengthHomomorphism(l1, l2)
          lengthHomomorphism(l2, l1) //ensure length
          biggerSublist(l1, l2)//ensure l1 == l2
          antisymmetry(l1.tail, l2.tail)
         
    }
    /* TODO: Prove me */
  }.ensuring(_ =>
    l1 == l2
  )

  /* 
  * ++ is the list concatenation operator.
  * It is defined here: 
  * https://github.com/epfl-lara/stainless/blob/64a09dbc58d0a41e49e7dffbbd44b234c4d2da59/frontends/library/stainless/collection/List.scala#L46
  */
  def extendRight[T](l1: List[T], l2: List[T]): Unit = {
    (l1, l2) match {
      case (Nil(), _) => ()
      case (Cons(x, xs), _) =>
        extendRight(l1.tail, l2)
    }
    /* TODO: Prove me */
  }.ensuring(_ => 
    sublist(l1, l1 ++ l2)  
  )

  def extendLeft[T](l1: List[T], l2: List[T]): Unit = {
    (l1, l2) match {
      case (Nil(), _) => 
        reflexivity(l2)
      case (Cons(x, xs), _) =>
        
        extendLeft(l1.tail, l2)
    }

    /* TODO: Prove me */
  }.ensuring(_ => 
    sublist(l2, l1 ++ l2)  
  )

  def prepend[T](l: List[T], l1: List[T], l2: List[T]): Unit = {
    require(sublist(l1, l2))
    (l) match {
      case Nil() => 
        ()
      case Cons(x, xs) =>
        prepend(xs, l1, l2)
    }
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l ++ l1, l ++ l2)  
  )

  def append[T](l1: List[T], l2: List[T], l: List[T]): Unit = { //make sure each construction in proof trace need to be proved
    require(sublist(l1, l2))
    (l1, l2) match {

      case (Nil(), _) => 
        extendLeft(l2, l)
      case (_, Nil()) =>
        extendRight(l1, l)
      case (Cons(x, xs), Cons(y, ys)) =>
        if(x == y) {
          tails(l1, l2)
          append(l1.tail, l2.tail, l)
        } else {
          if(sublist(l1, l2.tail)) then append(l1, l2.tail, l)
        }
    }
    /* TODO: Prove me */
  }.ensuring(_ =>
    sublist(l1 ++ l, l2 ++ l)  
  )
}

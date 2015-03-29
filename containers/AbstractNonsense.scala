package containers

/**
 * Created by christopheroliver on 3/15/15.
 */

trait Functor[F[_]] {
  def map[A, B](xs: F[A], f: A=>B): F[B]
}

trait NaturalTransformation[F[_], G[_]] {
  def apply[X](xs: F[X]): G[X]
}

trait Associative[F[_]] extends NaturalTransformation[({type λ[α] = F[F[α]]})#λ, F] {
  def flatten[X](xs: F[F[X]])(implicit f: Functor[F]): F[X]
}

trait Distributive[F[_], G[_]] extends NaturalTransformation[F, G] {
  def transpose[X](xs: F[G[X]])(implicit f: Functor[F], g: Functor[G]): G[F[X]]
}

case class VerticalInterchange[F[_], G[_], H[_]] () {
  def vertical[X](n1: NaturalTransformation[F, G], n2: NaturalTransformation[G, H]):
  NaturalTransformation[F, H] = {
    new NaturalTransformation[F, H] {
      override def apply[X](f: F[X]): H[X] = {
        n2(n1(f))
      }
    }
  }
}

case class HorizontalInterchange[F[_], G[_], H[_], I[_]](val f: Functor[F],
                                                         val h: Functor[H]) {
  type FG[X] = F[G[X]]
  type HI[X] = H[I[X]]

  def innerThenOuter(n1: NaturalTransformation[F, H],
                     n2: NaturalTransformation[G, I]): NaturalTransformation[FG, HI] = {
    new NaturalTransformation[FG, HI] {
      override def apply[X](x: F[G[X]]): H[I[X]] = {
        n1(f.map(x, (y: G[X]) => n2(y)))
      }
    }
  }

  def outerThenInner(n1: NaturalTransformation[F, H],
                     n2: NaturalTransformation[G, I]):  NaturalTransformation[FG, HI] = {
    new NaturalTransformation[FG, HI] {
      override def apply[X](x: F[G[X]]): H[I[X]] = {
        val q: H[G[X]] = n1(x)
        h.map(q, (gs: G[X])=> {
          n2(gs)
        })
      }
    }
  }

}

object AbstractNonsense {

  type ==>[F[_], G[_]] = NaturalTransformation[F, G]

  val optionFunctor: Functor[Option] = {
    new Functor[Option] {
      override def map[A, B](xs: Option[A], f: (A) => B): Option[B] = {
        for (x <- xs) yield f(x)
      }
    }
  }

  val listFunctor: Functor[List] = {
    new Functor[List] {
      override def map[A, B](xs: List[A], f: (A) => B): List[B] = {
        for (x <- xs) yield f(x)
      }
    }
  }

  def main(argv: Array[String]): Unit = {

    val optionToList: Option ==> List = {
      new (Option ==> List) {
        override def apply[X](xs: Option[X]): List[X] = {
          xs match {
            case None => List()
            case Some(x) => List(x)
          }
        }
      }
    }

    val listToOption: NaturalTransformation[List, Option] = {
      new NaturalTransformation[List, Option] {
        override def apply[X](xs: List[X]): Option[X] = {
          if (xs.length > 0) Some(xs.head) else None
        }
      }
    }
    
    val reverse: NaturalTransformation[List, List] = new NaturalTransformation[List, List] {
      override def apply[X](xs: List[X]): List[X] = {
        xs.reverse
      }
    }
    val vert = new VerticalInterchange[List, List, List]()
    val horiz = new HorizontalInterchange[List, List, List, List](listFunctor, listFunctor)
    val id1 = vert.vertical(reverse, reverse)
    val comm = HorizontalInterchange[Option, List, List, Option](optionFunctor, listFunctor)
    val transpose = comm.outerThenInner(optionToList, listToOption)
    val xs = List("a", "b", "c")
    println(id1(xs))
    println(transpose(Some(List("x"))))
    println(comm.innerThenOuter(optionToList, listToOption).apply(Some(List("y"))))
    //println(horiz.innerThenOuter(List(List(xs))))
  }
}

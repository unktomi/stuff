package containers

import containers.AbstractNonsense.Id
import lenses.Prisms._
/*
 * Created by christopheroliver on 3/15/15.
 */

trait ExponentialFunctor[F[_]] {
  def xmap[A, B](xs: F[A], f: A=>B, g: B=>A): F[B]
}

trait Functor[F[_]] extends ExponentialFunctor[F] {
  def map[A, B](xs: F[A], f: A=>B): F[B]
  override def xmap[A, B](xs: F[A], f: A=>B, g:B=>A): F[B] = map(xs, f)
}

trait ContraFunctor[F[_]] extends ExponentialFunctor[F] {
  def contramap[A, B](xs: F[B], f: A=>B): F[A]
  override def xmap[A, B](xs: F[A], f: A=>B, g:B=>A): F[B] = contramap(xs, g)
}

trait NaturalTransformation[F[_], G[_]] {
  def apply[X](xs: F[X]): G[X]
}

trait Associative[F[_]] extends NaturalTransformation[({type λ[α] = F[F[α]]})#λ, F] {
  override def apply[X](xs: F[F[X]]): F[X] = flatten(xs)
  def flatten[X](xs: F[F[X]])(implicit f: Functor[F]): F[X]
}

trait Pointed[F[_]] extends NaturalTransformation[Id, F] {
  override def apply[X](xs: Id[X]): F[X] = coextract(xs)
  def coextract[X](xs: Id[X]): F[X]
}

trait Coassociative[F[_]] extends NaturalTransformation[F, ({type λ[α] = F[F[α]]})#λ] {
  override def apply[X](xs: F[X]): F[F[X]] = duplicate(xs)
  def duplicate[X](xs: F[X]): F[F[X]]
}

trait Copointed[F[_]] extends NaturalTransformation[F, Id] {
  override def apply[X](xs: F[X]): Id[X] = extract(xs)
  def extract[X](xs: F[X]): Id[X]
}

trait Distributive[F[_], G[_]] extends NaturalTransformation[({type λ[α] = F[G[α]]})#λ, ({type λ[α] = G[F[α]]})#λ] {
  override def apply[X](xs: F[G[X]]): G[F[X]] = transpose(xs)
  def transpose[X](xs: F[G[X]])(implicit f: Functor[F], g: Functor[G]): G[F[X]]
}

case class VerticalInterchange[F[_], G[_], H[_]] () {
  def compose[X](n1: NaturalTransformation[F, G], n2: NaturalTransformation[G, H]):
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

  type Monad[F[_]] = (Pointed[F], Associative[F])
  type Comonad[F[_]] = (Copointed[F], Coassociative[F])

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
  
  type Id[X] = X

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

  val listMonad =
    (new Pointed[List] {
      override def coextract[X](xs: Id[X]): List[X] = List(xs)
    },
    new Associative[List] {
      override def flatten[X](xs: List[List[X]])(implicit f: Functor[List]): List[X] = {
        xs.flatten
      }
    })

  trait Observer[A] {
    var last: Option[A] = None
    def onNext(x: A): Unit
    def getLastObserved: Option[A] = last
    def raise(x: A): Unit = { last = Some(x); onNext(x) }
    def handle(y: Unit): Either[Unit, A] = getLastObserved match {
      case Some(x) => Right(x)
      case _ => Left(())
    }
  }

  trait Observable[A] extends Observer[Observer[A]] {
    def subscribe(x: Observer[A]): Unit = onNext(x)
  }

  val observerFunctor = new ContraFunctor[Observer] {
    override def contramap[A, B](xs: Observer[B], f: (A) => B): Observer[A] = {
      new Observer[A] {
        override def onNext(x: A): Unit = {
          xs.onNext(f(x))
        }
      }
    }
  }

  val observableFunctor = new Functor[Observable] {
    override def map[A, B](xs: Observable[A], f: (A) => B): Observable[B] = {
      new Observable[B] {
        override def onNext(y: Observer[B]): Unit = {
          xs.onNext(new Observer[A] {
            override def onNext(x: A): Unit = {
              y.onNext(f(x))
            }
          })
        }
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

    val listToOption: List ==> Option = {
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
    val id1 = vert.compose(reverse, reverse)
    val comm = HorizontalInterchange[Option, List, List, Option](optionFunctor, listFunctor)
    val transpose = comm.outerThenInner(optionToList, listToOption)
    val xs = List("a", "b", "c")
    println(id1(xs))
    val ys = Some(List("y"))
    println(transpose(ys))
    println(comm.innerThenOuter(optionToList, listToOption).apply(ys))
  }
}

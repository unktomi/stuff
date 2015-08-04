package containers

import containers.AbstractNonsense.Id
import lenses.Prisms._

import scala.collection.mutable

trait Monoid[A] {
  def empty: A
  def add(x: A, y: A): A
}

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
  def flatten[X](xs: F[F[X]]): F[X]
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
  def transpose[X](xs: F[G[X]]): G[F[X]]
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

trait Ran[G[_], H[_], A] {
  def apply[B](f: A => G[B]): H[B]
}

trait Lan[G[_], H[_], A] {
  def apply[B]: (G[B] => A, H[B])
}

trait Yoneda[F[_], A] extends Ran[Id, F, A] {
  override def apply[B](f: A => B): F[B]
}

trait Coyoneda[F[_], A] extends Lan[Id, F, A] {
  override def apply[B]: (B => A, F[B])
  def map[C](f: A=>C): Coyoneda[F, C] = {
    val self = this
    new Coyoneda[F, C] {
      override def apply[B]: ((B) => C, F[B]) = {
        val g = self.apply[B]
        (f.compose(g._1), g._2)
      }
    }
  }
}

case class Writer[A, W](output: W, value: A)(implicit w: Monoid[W]) {
  def map[B](f: A=>B): Writer[B, W] = {
    new Writer[B, W](output, f(value))
  }
  def flatMap[B](f: A=> Writer[B, W]): Writer[B, W] = {
    val w1 = f(value)
    new Writer[B, W](w.add(w1.output, output), w1.value)
  }
}

abstract class Cowriter[A, W](implicit w: Monoid[W]) extends (W=>A) {
  def extract: A = apply(w.empty)
  def map[B](f: A=>B): Cowriter[B, W] = {
    val self = this
    new Cowriter[B, W] {
      override def apply(v1: W): B = {
        f(self(v1))
      }
    }
  }
  def flatMap[B](f: A=>Cowriter[B, W]): Cowriter[B, W] = {
    coflatMap((x: Cowriter[A, W])=> f(x.extract).extract)
  }
  def coflatMap[B](f: Cowriter[A, W] => B): Cowriter[B, W] = {
    val self = this
    new Cowriter[B, W] {
      override def apply(v1: W): B = {
        f(new Cowriter[A, W] {
          override def apply(v2: W): A = {
            self.apply(w.add(v1, v2))
          }
        })
      }
    }
  }
}



// Codensity Monad
trait Codensity[F[_], A] extends Ran[F, F, A] {
  override def apply[R](k: A=>F[R]): F[R]
  def map[B](f: A=>B): Codensity[F, B] = {
    val self = this
    new Codensity[F, B] {
      override def apply[R](k1: (B) => F[R]): F[R] = {
        self.apply((x: A)=> {
          k1(f(x))
        })
      }
    }
  }
  def flatMap[B](f: A=>Codensity[F, B]): Codensity[F, B] = {
    val self = this
    new Codensity[F, B] {
      override def apply[R](k1: (B) => F[R]): F[R] = {
        self.apply((x: A)=> {
          f(x).apply((y: B)=>k1(y))
        })
      }
    }
  }
}

// Density Comonad
trait Density[F[_], A] extends Lan[F, F, A] {
  override def apply[B]: ((F[B]) => A, F[B])
  def extract: A = { val j = apply[A]; j._1(j._2) }
  def map[B](f: A=>B): Density[F, B] = {
    val self = this
    new Density[F, B] {
      override def apply[C]: ((F[C]) => B, F[C]) = {
        val j = self.apply[C]
        (f.compose(j._1), j._2)
      }
    }
  }
  def coflatMap[B](f: Density[F, A]=>B): Density[F, B] = {
    val self = this
    new Density[F, B] {
      override def apply[C]: ((F[C]) => B, F[C]) = {
        val j = self.apply[C]
        ((xs:F[C])=>f(self), j._2)
      }
    }
  }
}


trait RxSubject extends Density[({type G[A] = A=>Unit})#G, Unit] {
  override def apply[B]: ((B => Unit) => Unit, B => Unit) = {
    val subscribers = new mutable.WeakHashMap[B=>Unit, Unit]
    ((subscriber: B => Unit)=> subscribers.put(subscriber, ()), (msg: B)=> for { sub <- subscribers.keySet } sub.apply(msg))
  }
}

case class SubjectW[W](implicit m: Monoid[W]) extends Density[({type λ[α] = α => W})#λ, W] {
  override def apply[B]: (((B) => W) => W, (B) => W) = {
    val subscribers = new mutable.WeakHashMap[B=>W, W]
    ((k: B=>W)=> {subscribers.put(k, m.empty); m.empty},
      (x: B)=> {
        var w0 = m.empty
        for {
          (sub, w) <- subscribers
        } {
          w0 = m.add(sub(x), w)
        }
        w0
      })
  }
}

object AbstractNonsense {

  def UnitMonoid: Monoid[Unit] = new Monoid[Unit] {
    def empty: Unit = ()
    def add(x: Unit, y: Unit): Unit = ()
  }

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
      override def flatten[X](xs: List[List[X]]): List[X] = {
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

    def subject[A] = new RxSubject {}.apply[A]
    val s = subject[Int]
    s._1((x: Int)=>println("received "+x))
    s._2(100)
  }


}

package containers

import containers.AbstractNonsense.{==>, Id}


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

trait Monad[F[_]] extends Functor[F] {
  def unit[A](x: A): F[A]
  def join[A](xs: F[F[A]]): F[A] = flatMap(xs, (x:F[A])=>x)
  def flatMap[A, B](xs: F[A], f: A=>F[B]): F[B] = join(map(xs, f))
}

trait Comonad[F[_]] extends Functor[F] {
  def extract[A](xs: F[A]): A
  def duplicate[A](xs: F[A]): F[F[A]] = coflatMap[A, F[A]](xs, (x:F[A])=>x)
  def coflatMap[A, B](xs: F[A], f: F[A]=>B): F[B] = map(duplicate(xs), f)
}
 /*
trait MonadFail[F[_]] extends Monad[F] {
  def raise[A](x: A): F[A]
}

trait MonadExc[F[_]] extends MonadFail[F] {
  def handle[A](xs: F[A]): Either[A, F[A]]
}

trait ComonadState[F[_]] extends Comonad[F] {
  def get[A](xs: F[A]): A
  def put[A](xs: F[A], x: A): F[A]
}
 */
trait ContraFunctor[F[_]] extends ExponentialFunctor[F] {
  def contramap[A, B](xs: F[B], f: A=>B): F[A]
  override def xmap[A, B](xs: F[A], f: A=>B, g:B=>A): F[B] = contramap(xs, g)
}

trait NaturalTransformation[F[_], G[_]] {
  def apply[X](xs: F[X]): G[X]
}

trait Associative[F[_]] extends NaturalTransformation[({type G[A] = F[F[A]]})#G, F] {
  override def apply[X](xs: F[F[X]]): F[X] = flatten(xs)
  def flatten[X](xs: F[F[X]]): F[X]
}

trait Pointed[F[_]] extends NaturalTransformation[Id, F] {
  override def apply[X](xs: Id[X]): F[X] = coextract(xs)
  def coextract[X](xs: Id[X]): F[X]
}

trait Coassociative[F[_]] extends NaturalTransformation[F, ({type G[A] = F[F[A]]})#G] {
  override def apply[X](xs: F[X]): F[F[X]] = duplicate(xs)
  def duplicate[X](xs: F[X]): F[F[X]]
}

trait Copointed[F[_]] extends NaturalTransformation[F, Id] {
  override def apply[X](xs: F[X]): Id[X] = extract(xs)
  def extract[X](xs: F[X]): Id[X]
}

trait Distributive[F[_], G[_]] extends NaturalTransformation[({type H[A] = F[G[A]]})#H, ({type I[A] = G[F[A]]})#I] {
  override def apply[X](xs: F[G[X]]): G[F[X]] = transpose(xs)
  def transpose[X](xs: F[G[X]]): G[F[X]]
}

case class VerticalComposition[F[_], G[_], H[_]] () {
  def compose[X](n1: NaturalTransformation[F, G], n2: NaturalTransformation[G, H]):
  NaturalTransformation[F, H] = {
    new NaturalTransformation[F, H] {
      override def apply[X](f: F[X]): H[X] = {
        n2(n1(f))
      }
    }
  }
}

case class HorizontalComposition[F[_], G[_], H[_], I[_]](val f: Functor[F],
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

// Right Kan Extension

trait Ran[G[_], H[_], A] {
  def apply[T](f: Id[A] => G[T]): H[T]
}

trait LeftKanExtension[G[_], H[_], A] {
  def apply[T]: (H[T], G[T]=>Id[A])
  def map[B](f: A=>B): LeftKanExtension[G, H, B] = {
    val self = this
    new LeftKanExtension[G, H, B] {
      override def apply[R]: (H[R], (G[R]) => B) = {
        val t = self.apply[R]
        (t._1, (xs: G[R])=>f(t._2(xs)))
      }
    }
  }

  def extract(n: H==>G) = {
    val t = apply[Nothing]
    t._2(n.apply[Nothing](t._1))
  }

  def coflatMap[B](n: H==>G, f: A=>LeftKanExtension[G, H, B]): LeftKanExtension[G, H, B] = {
    val self = this
    new LeftKanExtension[G, H, B] {
      override def apply[R]: (H[R], (G[R]) => B) = {
        val t = self.apply[R]
        (t._1, (xs: G[R])=>f(t._2(xs)).extract(n))
      }
    }
  }
}

// Left Kan Extension

trait LanTuple[G[_], H[_], A, B] {
  def peek(xs: G[B]): A
  def pos: H[B]
  def map[C](f: A=>C): LanTuple[G, H, C, B] = {
    val self = this
    new LanTuple[G, H, C, B] {
      override def peek(xs: G[B]): C = f(self.peek(xs))
      override def pos: H[B] = self.pos
    }
  }
}

trait Lan[G[_], H[_], A] {
  def apply: LanTuple[G, H, A, _]
}

trait Yoneda[F[_], A] extends Ran[Id, F, A] {
  override def apply[B](f: A => B): F[B]
}

trait Coyoneda[F[_], A] extends Lan[Id, F, A] {

  override def apply: LanTuple[Id, F, A, _]

  def map[C](f: A=>C): Coyoneda[F, C] = {
    val self = this
    new Coyoneda[F, C] {
      override def apply: LanTuple[Id, F, C, _] = {
        self.apply.map(f)
      }
    }
  }
}

// Constant Functor
case class Constant[C, A](val const: C) {
  def map[B](f: A=>B): Constant[C, B] = {
    Constant[C, B](const)
  }
}

// Self-dual continuation monad
trait Cont0[A] extends Ran[Id, Id, A] {
  override def apply[R](f: A=>R): R
  def extract: A = apply(identity[A](_))
  def map[B](f: A=>B): Cont0[B] = {
    val self = this
    new Cont0[B] {
      override def apply[R](k: (B) => R): R = {
        self.apply((x: A)=>k(f(x)))
      }
    }
  }
  def flatMap[B](f: A=>Cont0[B]): Cont0[B] = {
    val self = this
    new Cont0[B] {
      override def apply[R](k: (B) => R): R = {
        self.apply((x: A)=>f(x).apply(k))
      }
    }
  }
  def coflatMap[B](f: Cont0[A]=>B): Cont0[B] = {
    val self = this
    new Cont0[B] {
      override def apply[R](k: (B) => R): R = {
        k(f(self))
      }
    }
  }
}

trait Cocont0[A] extends LeftKanExtension[Id, Id, A] {
  override def apply[T]: (T, T => A) // unimplementable
}

// Continuation Monad = Ran[Constant[R], Constant[R], A]

case class Cont[R, A](k: (A=>R)=>R) extends Ran[({type G[X] = Constant[R, X]})#G, ({type G[X] = Constant[R, X]})#G, A] {

  override def apply[B](f: A => Constant[R, B]): Constant[R, B] = {
    Constant(k((x:A)=>f(x).const))
  }
  
  def map[B](f: A=>B): Cont[R, B] = {
    Cont[R, B]((k1: B=>R)=>k((x:A)=>k1(f(x))))
  }

  def flatMap[B](f: A=>Cont[R, B]): Cont[R, B] = {
    Cont[R, B]((k1: B=>R)=>k((x:A)=> { val c = f(x); c.k(k1) }))
  }
}

// Cocontinuation Comonad = Lan[Constant[R], Constant[R], A]
case class Cocont[R, A] (get: R, set: R=>A) extends Lan[({type G[X] = Constant[R, X]})#G, ({type G[X] = Constant[R, X]})#G, A] {

  override def apply: LanTuple[({type G[X] = Constant[R, X]})#G, ({type G[X] = Constant[R, X]})#G, A, Nothing] = {
    new LanTuple[({type G[X] = Constant[R, X]})#G, ({type G[X] = Constant[R, X]})#G, A, Nothing] {
      override def peek(xs: Constant[R, Nothing]): A = set(xs.const)
      override def pos: Constant[R, Nothing] = Constant(get)
    }
  }

  def extract: A = {
    val t = apply
    t.peek(t.pos)
  }

  def map[B](f: A=>B): Cocont[R, B] = {
    Cocont[R, B](get, set.andThen(f))
  }

  def coflatMap[B](f: Cocont[R, A]=> B): Cocont[R, B] = {
    val self = this
    Cocont[R, B](get, (x: R)=>f(Cocont[R, A](x, set)))
  }
}

// Free Monad of a functor F = Pure A or Impure F[Free[F, A]]
trait Free[F[_], A] {
  def map[B](f: A=>B): Free[F, B]
  def flatMap[B](f: A=>Free[F, B]): Free[F, B]
}

case class Pure[F[_], A](x: A) extends Free[F, A] {
  def map[B](f: A=>B): Free[F, B] = Pure(f(x))
  def flatMap[B](f: A=>Free[F, B]): Free[F, B] = f(x)
}

case class Impure[F[_], A](xs: F[Free[F, A]])(implicit fun: Functor[F]) extends Free[F, A] {
  def map[B](f: A=>B): Free[F, B] = Impure[F, B](fun.map(xs, (x: Free[F, A])=> x.map(f)))
  def flatMap[B](f: A=>Free[F, B]): Free[F, B] = Impure[F, B](fun.map(xs, (x: Free[F, A])=> x.flatMap(f)))
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

trait DensityTuple[F[_], A, B] extends LanTuple[F, F, A, B] {
  def extract: A = peek(pos)
  def coflatMap[C](f: DensityTuple[F, A, B]=>C): DensityTuple[F, C, B] = {
    val self = this
    new DensityTuple[F, C, B] {
      override def peek(xs: F[B]): C = {
        f(self)
      }
      override def pos: F[B] = self.pos
    }
  }
  override def map[C](f: A => C): DensityTuple[F, C, B] = {
    val self = this
    new DensityTuple[F, C, B] {
      override def peek(xs: F[B]): C = {
        f(self.peek(xs))
      }
      override def pos: F[B] = self.pos
    }
  }
}

trait Density[F[_], A] extends Lan[F, F, A] {
  override def apply: DensityTuple[F, A, _]
  def extract: A = { val j = apply; j.extract }
  def map[B](f: A=>B): Density[F, B] = {
    val self = this
    new Density[F, B] {
      override def apply: DensityTuple[F, B, _] = {
        val j = self.apply
        j.map(f)
      }
    }
  }

  def duplicate: Density[F, Density[F, A]] = {
    coflatMap(identity(_))
  }

  def flatMap[B](f: A=>Density[F, B]): Density[F, B] = {
    map(f).extract
  }

  def coflatMap[B](f: Density[F, A]=>B): Density[F, B] = {
    val self = this
    new Density[F, B] {
      override def apply: DensityTuple[F, B, _] = {
        val d = self.apply
        d.coflatMap((t)=>f(self))
      }
    }
  }
}

trait Iterator[F[_], A] extends Codensity[({type G[A] = Density[F, A]})#G, A] {
  override def apply[R](k: (A) => Density[F, R]): Density[F, R]
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
  /*
  def eitherMonadExc[A, B] = new MonadExc[({type G[A] = Either[A, B]})#G] {
    override def handle[A](xs: Either[A, B]): Either[A, Either[A, B]] = {
      xs match {
        case Left(x) => Left(x)
        case Right(y) => Right(xs)
      }
    }

    override def raise[A](x: A): Either[A, B] = Left(x)

    override def unit[A](x: A): Either[A, B] = Left(x)

    override def map[A, C](xs: Either[A, B], f: (A) => C): Either[C, B] = {
      xs match {
        case Left(x) => Left(f(x))
        case Right(y) => Right(y)
      }
    }
  }

  def listMonoid = new Monoid[List] {
    override def add(x: List, y: List): List = x ++ y
    override def empty: List = List()
  }

  def unitMonoid = new Monoid[Unit] {
    override def add(x: Unit, y: Unit): Unit = ()
    override def empty: Unit = ()
  }

  type StateType[S] = ({type G[A] = S=>(S, A)})#G

  type PairType[B] = ({type G[A] = (A, B)})#G

  def pairCommonadState[A, B]: ComonadState[PairType[B]] =
    new ComonadState[({type G[A] = (A, B)})#G] {
      override def get[A](xs: (A, B)): A = xs._1
      override def put[A](xs: (A, B), x: A): (A, B) = (x, xs._2)
      override def map[A, C](xs: (A, B), f: (A) => C): (C, B) = {
        (f(xs._1), xs._2)
      }
      override def extract[A](xs: (A, B)): A = get(xs)
    }
     */
  def main(argv: Array[String]): Unit = {
    if (true) {
      test
      return
    }
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
    val vert = new VerticalComposition[List, List, List]()
    val horiz = new HorizontalComposition[List, List, List, List](listFunctor, listFunctor)
    val id1 = vert.compose(reverse, reverse)
    val comm = HorizontalComposition[Option, List, List, Option](optionFunctor, listFunctor)
    val transpose = comm.outerThenInner(optionToList, listToOption)
    val xs = List("a", "b", "c")
    println(id1(xs))
    val ys = Some(List("y"))
    println(transpose(ys))
    println(comm.innerThenOuter(optionToList, listToOption).apply(ys))
    testDensity
  }

  def codensityMonad[F[_]](implicit m: Monad[F]): Monad[({type G[A] = Codensity[F, A]})#G] = {
    new Monad[({type G[A] = Codensity[F, A]})#G] {
      override def unit[A](x: A): Codensity[F, A] = codense(x)(m)
      override def map[A, B](xs: Codensity[F, A], f: (A) => B): Codensity[F, B] = {
        xs.map(f)
      }
    }
  }

  def testDensity: Unit = {
    val w: Comonad[List] = new Comonad[List] {
      override def extract[A](xs: List[A]): A = xs.head
      override def map[A, B](xs: List[A], f: (A) => B): List[B] = xs.map(f)
    }
    val m: Monad[List] = new Monad[List] {
      override def unit[A](x: A): List[A] = List(x)
      override def map[A, B](xs: List[A], f: (A) => B): List[B] = xs.map(f)
    }
    val d = dense(List(1, 2, 3))(w)
    println(d.extract)
    val z = codense(1)(m)

    val it = iter(List(1, 2, 3))(w)


  }

  def iter[F[_], A](xs: F[A])(implicit w: Comonad[F]): Iterator[F, A] = {
    new Iterator[F, A] {
      override def apply[R](k: (A) => Density[F, R]): Density[F, R] = {
        dense(xs).flatMap(k)
      }
    }
  }

  def codense[F[_], A](x: A)(implicit w: Monad[F]): Codensity[F, A] = {
    new Codensity[F, A] {
      override def apply[R](k: (A) => F[R]): F[R] = {
        w.flatMap(w.unit(x), k)
      }
    }
  }


  def dense[F[_], A](xs: F[A])(implicit w: Comonad[F]): Density[F, A] = {
    new Density[F, A] {
      override def apply: DensityTuple[F, A, _] = {
        new DensityTuple[F, A, A] {
          override def peek(xs: F[A]): A = w.extract(xs)
          override def pos: F[A] = xs
        }
      }
    }
  }

  // unit of Cont monad
  def negate[R](x: R): Cont[R, R] = {
    Cont((k)=>k(x))
  }

  // delimited continuations

  def reset[R](k: Cont[R, R]): R = {
    k.k(identity[R])
  }

  def shift[A, R](k: (A=>R)=>R): Cont[R, A] = {
    Cont[R, A](k)
  }

  def test: Unit = {
    val n = reset(for {
      i <- negate(10)
      j <- shift[Int, Int]((k)=>k(100))
      z <- shift[Int, Int]((k)=>42)
    } yield j+i)
    println(n)
  }
}

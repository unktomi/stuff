package contractive

import containers.{Functor, Monad, Comonad}

trait Stream[A] {

  def now: A
  def later: Stream[A]

  def prepend(x: A): Stream[A] = {
    val self = this
      new Stream[A] {
        val now = x
        val later = self
      }
  }

  def map[B](f: A=>B): Stream[B] = {
    Contractive.unfold(this, (xs:Stream[A])=>f(xs.now), (xs: Stream[A], y: B)=> xs.later)
  }

  def flatMap[B](f: A=>Stream[B]): Stream[B] = {
    map(f).extract
  }

  def extract: A = now

  def duplicate: Stream[Stream[A]] = {
    coflatMap(identity(_))
  }

  def coflatMap[B](f: Stream[A] => B): Stream[B] = {
    Contractive.unfold(this, (xs:Stream[A])=>f(xs), (xs: Stream[A], y: B)=> xs.later)
  }

  def fold[B](z: B, f: (B, A)=>B): Stream[B] = {
    Contractive.fold(this, z, f)
  }

  def take(n: Int): List[A] = {
    now :: (if (n == 0) List() else later.take(n-1))
  }

}

case class Cont[R, A](run: (A => R) => R) {
  def flatMap[B](f: A => Cont[R, B]): Cont[R, B] =
    Cont(k => run(a => f(a) run k))
  def map[B](f: A => B): Cont[R, B] =
    Cont(k => run(a => k(f(a))))
}

trait Event[A] {
  def apply[C](now: A=>C, later: Event[A] => C): C
}

case class Now[A](val now: A) extends Event[A] {
  override def apply[C](now: A=>C, later: Event[A] => C): C = {
     now(this.now)
  }
}

case class Later[A]() extends Event[A] {
  override def apply[C](now: A=>C, later: Event[A] => C): C = {
    later(this)
  }
}

trait ChurchFreeMonad[F[_], +A] {
  def apply[R](now: A => R, later: F[R] => R): R

  def map[B](f: A => B): ChurchFreeMonad[F, B] = {
    val self = this
    new ChurchFreeMonad[F, B] {
      override def apply[R](now: (B) => R, later: (F[R]) => R): R = {
        self.apply((x: A) => now(f(x)), (xs: F[R]) => later(xs))
      }
    }
  }

  def flatMap[B](f: A => ChurchFreeMonad[F, B]): ChurchFreeMonad[F, B] = {
    val self = this
    new ChurchFreeMonad[F, B] {
      override def apply[R](now: (B) => R, later: (F[R]) => R): R = {
        self.apply((x: A) => f(x).apply(now, later), later)
      }
    }
  }
}

trait ChurchCofreeComonad[F[_], A] {
  def fun: Functor[F]
  def apply[R](nowAndLater: (A, F[A])=>R): R
  def map[B](f: A=>B): ChurchCofreeComonad[F, B] = {
    val self = this
    new ChurchCofreeComonad[F, B] {
      def fun = self.fun
      override def apply[R](nowAndLater: (B, F[B]) => R): R = {
        self.apply((now, later)=>nowAndLater(f(now), fun.map(later, f)))
      }
    }
  }
  def extract: A = apply((now, later)=>now)
  def flatMap[B](f: A=>ChurchCofreeComonad[F, A]): ChurchCofreeComonad[F, A] = map(f).extract
}

// Indexed store comonad
trait Store[I, O, R] {
  def pos: O
  def peek(index: I): R
  def map[B](f: R=>B): Store[I, O, B] = {
    val self = this
    new Store[I, O, B] {
      override def peek(index: I): B = f(self.peek(index))
      override def pos: O = self.pos
    }
  }
  def flatMap[B](f: R=>Store[I, O, B]): Store[I, O, B] = {
    val self = this
    new Store[I, O, B] {
      override def peek(index: I): B = f(self.peek(index)).peek(index)
      override def pos: O = self.pos
    }
  }
}

// Free monad over the indexed store comonad
trait Iterator[I, O, A] {
  def apply[R](now: A => R, later: Store[I, O, A] => R): R
  def map[B](f: A => B): Iterator[I, O, B] = {
    val self = this
    new Iterator[I, O, B] {
      override def apply[R](now: (B) => R, later: (Store[I, O, B]) => R): R = {
        self.apply((x: A) => now(f(x)), (s: Store[I, O, A]) => later(s.map(f)))
      }
    }
  }

  def flatMap[B](f: A => Iterator[I, O, B]): Iterator[I, O, B] = {
    val self = this
    new Iterator[I, O, B] {
      override def apply[R](now: (B) => R, later: (Store[I, O, B]) => R): R = {
        self.apply((x: A) => f(x).apply(now, later), (s: Store[I, O, A]) => {
          later(new Store[I, O, B] {
            override def peek(index: I): B = {
              val y = f(s.peek(index))
              y.apply(identity[B](_), (s1) => s1.peek(index))
            }
            override def pos: O = s.pos
          })
        })
      }
    }
  }

}


trait Iter[I, O, A] {
  def apply[R](now: A=>R, later: (O)=>(I=>R)=>R): R
  def map[B](f: A=>B): Iter[I, O, B] = {
    val self = this
    new Iter[I, O, B] {
      override def apply[R](now: (B) => R, later: (O) => ((I) => R) => R): R = {
        self.apply((x: A)=>now(f(x)), (o: O)=>later(o))
      }
    }
  }
  def flatMap[B](f: A=>Iter[I, O, B]): Iter[I, O, B] = {
    val self = this
    new Iter[I, O, B] {
      override def apply[R](now: (B) => R, later: (O) => ((I) => R) => R): R = {
        self.apply((x: A)=> {
          val nested = f(x)
          nested.apply(now, (o)=> {
            later(o)
          })
        }, later)
      }
    }
  }
}


trait IOK[I, O, R] {
  def apply(ffi: O=>I, o: O, k: I=>R): R
}

trait IO[A] {
  def apply[R](k: A => R, iok: IOK[_, _, R]): R
  def unsafePerformIO = apply(identity(_), new IOK[A, A, A] {
    override def apply(ffi: (A) => A, o: A, k: (A) => A): A = k(ffi(o))
  })
  def map[B](f: A=>B): IO[B] = {
    val self = this
    new IO[B] {
      override def apply[R](k: (B) => R, iok: IOK[_, _, R]): R = {
        self.apply((x:A)=>k(f(x)), iok)
      }
    }
  }
  def flatMap[B](f: A=>IO[B]): IO[B] = {
    val self = this
    new IO[B] {
      override def apply[R](k: (B) => R, iok: IOK[_, _, R]): R = {
        self.apply((x:A)=>f(x).apply(k, iok), iok)
      }
    }
  }
}


/**
 * Created by christopheroliver on 8/9/15.
 */
object Contractive {

  def getChar: IO[Char] = new IO[Char] {
    override def apply[R](k: (Char) => R, iok: IOK[_, _, R]): R = {
      k(System.in.read().asInstanceOf[Char])
    }
  }

  def putChar(c: Char): IO[Unit] = {
    new IO[Unit] {
      override def apply[R](k: (Unit) => R, iok: IOK[_, _, R]): R = {
        k(System.out.write(c))
      }
    }
  }

  def yield1[A](x: A): Iter[Unit, A, Unit] = new Iter[Unit, A, Unit] {
    override def apply[R](now: (Unit) => R, then: (A) => ((Unit) => R) => R): R = {
      val k = then(x)
      k(now)
    }
  }

  def test1: Unit = {
    val xs = for {
      x <- yield1(1)
      y <- yield1(2)
      z <- yield1(3)
    } yield z

    xs.apply((u) => println("done"), (x: Int) => {
      println(x);
      (k: Unit => Unit) => k()
    })
  }

  type Id[A] = A


  def unfold[C, B](past: C, unfoldPresent: C => B, unfoldFuture: (C, B) => C): Stream[B] = {
    new Stream[B] {
      lazy val now = unfoldPresent(past)
      lazy val later = unfold(unfoldFuture(past, now), unfoldPresent, unfoldFuture)
    }
  }

  def repeat[A](x: A): Stream[A] = unfold[A, A](x, (_) => x, (_, _) => x)

  def fold[A, B](xs: Stream[A], z: B, f: (B, A) => B): Stream[B] = {
    unfold[(B, Stream[A]), B]((z, xs), (v: (B, Stream[A])) => f(v._1, v._2.now), (xs: (B, Stream[A]), y: B) => (y, xs._2.later))
  }


  def bad[A](xs: Stream[A]): Stream[Stream[A]] = {
    unfold[Stream[A], Stream[A]](xs, (ys) => ys, (ys, zs) => zs)
  }

  def nats: Stream[Int] = unfold[Int, Int](0, (x: Int) => x, (x: Int, _: Int) => x + 1)

  def fibs: Stream[Int] = unfold[(Int, Int), Int]((0, 1), (xs: (Int, Int)) => xs._1, (xs: (Int, Int), _) => (xs._2, xs._1 + xs._2))

  def main(argv: Array[String]): Unit = {
    println(nats.take(10))
    println(fibs.take(10))
    //val xs = bad(fibs)
    println(fold(repeat(1), 0, (x: Int, y: Int) => x + 1).take(10))

    println(fibs.map((_ + 1)).take(10))

    val d = for {
      x <- nats
      y <- nats
    } yield {
        println("x=" + x + ", y=" + y); x + y
      }
    println(d.take(10))

    println(for {
      s <- nats.duplicate.take(10)
    } yield s.now)

    testFib
  }

  def now[A](x: A): Cont[A, A] = unit(x)

  def unit[A](x: A): Cont[A, A] = Cont((k) => (k(x)))

  def callCC[R, A, B](f: (A => Cont[R, B]) => Cont[R, A]): Cont[R, A] =
    Cont(k => f(a => Cont(_ => k(a))) run k)

  def extract[A](xs: Cont[A, A]): A = {
    xs run (identity(_))
  }


  def subject[A]: (A => Unit, Cont[Unit, A]) = {
    val subscribers = new scala.collection.mutable.WeakHashMap[A => Unit, Unit]
    ((x) => {
      for {
        sub <- subscribers.keySet
      } sub(x)
    }, Cont((k: A => Unit) => subscribers.put(k, ())))
  }

  def mainCC = {

  }

  def unit[F[_], A](x: A): ChurchFreeMonad[F, A] = {
    new ChurchFreeMonad[F, A] {
      override def apply[R](now: (A) => R, later: (F[R]) => R): R = {
        now(x)
      }
    }
  }

  type Trampoline[+A] = ChurchFreeMonad[Function0, A]

  def bounce[A](x: A) = unit[Function0, A](x)

  def fib(n: Int): Trampoline[Int] = {
    if (n <= 1) bounce(n) else {
      for {
        x <- fib(n-1)
        y <- fib(n-2)
      } yield x + y
    }
  }

  def testFib: Unit = {
    val x = fib(100000)
    x.apply[Unit]((x: Int)=>println(x), (k: ()=>Unit)=>k)
  }


  type Consumer[A] = ChurchFreeMonad[({type G[B] = (A=>B)})#G, A]
  type Producer[A] = ChurchFreeMonad[({type G[B] = (A, B)})#G, A]
  def yeeld[A](x: A): Producer[A] = new Producer[A] {
    override def apply[R](now: (A) => R, later: ((A, R)) => R): R = {
      later(x, now(x))
    }
  }

  def await[A]: Consumer[A] = {
    new Consumer[A] {
      override def apply[R](now: A => R, later: (A => R) => R): R = {
         later((x:A)=>now(x))
      }
    }
  }

  def lift[F[_], A](xs: F[A])(implicit f: Functor[F]): ChurchFreeMonad[F, A] = {
    new ChurchFreeMonad[F, A] {
      override def apply[R](now: (A) => R, later: (F[R]) => R): R = {
          later(f.map(xs, now))
      }
    }
  }

  def colift[F[_], A](xs: F[A])(implicit w: Comonad[F]): ChurchCofreeComonad[F, A] = {
    new ChurchCofreeComonad[F, A] {
      override def fun = w
      override def apply[R](nowAndLater: (A, F[A]) => R): R = {
         nowAndLater(w.extract(xs), xs)
      }
    }
  }

}

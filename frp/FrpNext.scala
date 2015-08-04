package frp
import FrpNext._

// Nexttime
trait Nexttime[A]  {
  def when: Int
  def map[B](f: A=>B): Nexttime[B] = {
    val self = this
    nexttime(() => f(self.extract))
  }
  def extract: A
  def flatMap[B](f: A=>Nexttime[B]): Nexttime[B] = {
    coflatMap((x: Nexttime[A])=> f(x.extract).extract)
  }
  def coflatMap[B](f: Nexttime[A] => B): Nexttime[B] = {
    val self = this
    nexttime(() => f(self))
  }
  def zip[B, C](xs: Nexttime[B], f: (A, B)=>C): Nexttime[C] = {
    val self = this
    nexttime(()=> f(self.extract, xs.extract))
  }
}

// Now and Later
case class Stream[A](now: A, later: Nexttime[Stream[A]]) {
  def when = later.when - 1
  def extract: A = now
  def flatMap[B](f: A=>Stream[B]): Stream[B] = {
    coflatMap[B]((xs: Stream[A])=> {
      f(xs.now).extract
    })
  }
  def fold[B](z: B, f: (A, B)=> B): Stream[B] = {
    val x = f(now, z)
    Stream[B](x, for { s <- later } yield s.fold(x, f))
  }
  def map[B](f: A=>B): Stream[B] = Stream[B](f(now), later.map((xs: Stream[A])=> xs.map(f)))
  def coflatMap[B](f: Stream[A] => B): Stream[B] = {
    Stream[B](f(this), later.map((xs)=> xs.coflatMap(f)))
  }
  def zip[B, C](xs: Stream[B], f: (A, B)=>C): Stream[C] = {
    Stream[C](f(now, xs.now), nexttime[Stream[C]](() => later.extract.zip(xs.later.extract, f)))
  }
}

// Now or Later
trait Event[A] {
  def map[B](f: A=>B): Event[B]
  def flatMap[B](f: A=>Event[B]): Event[B]
}

case class Now[A](now: A) extends Event[A] {
  def map[B](f: A=>B): Event[B] = {
    Now(f(now))
  }
  def flatMap[B](f: A=>Event[B]): Event[B] = {
    f(now)
  }
}

case class Later[A](next: Nexttime[Event[A]]) extends Event[A] {
  def map[B](f: A=>B): Event[B] = {
    Later[B](next.map((e)=>e.map(f)))
  }
  def flatMap[B](f: A=>Event[B]): Event[B] = {
    Later[B](next.map((e)=>e.flatMap(f)))
  }
}

/**
 * Created by coliver on 7/31/2015.
 */
object FrpNext {
  var now: Integer = 0
  var thunks: List[Thunk[_]] = List()
  def tick(): Unit = {
    now = now + 1
    thunks = thunks.filter((thunk)=> {
      if (thunk.when != now) { println("thunk.when="+thunk.when+", now="+now); thunk.code = ()=> ??? }
      thunk.when == now
    })
  }

  def now[A](x: A): Event[A] = Now(x)
  def always[A](x: A): Stream[A] = Stream(x, nexttime(()=>always(x)))

  case class Thunk[A](var when: Int, var code: () => A) extends Nexttime[A] {
    def extract: A = if (when != now) ??? else code()
  }

  def nexttime[A](f: () => A): Nexttime[A] = {
    val thunk = Thunk[A](now+1, f)
    thunks = thunk :: thunks
    thunk
  }

  def delay[A](millis: Long, action: () => A): Event[A] = {
    if (millis <= 0) now(action()) else {
      val begin = System.currentTimeMillis()
      new Later(nexttime(() => {
        val elapsed = System.currentTimeMillis() - begin
        delay(millis - elapsed, action)
      }))
    }
  }

  def fix[A](f: Nexttime[A]=>A): A = f(nexttime[A](() => fix(f)))

  def take[A](xs: Stream[A], n: Int): List[A] = {
    if (n == 0) return List()
    tick()
    return xs.now :: take(xs.later.extract, n-1)
  }

  def sum(xs: Stream[Int]): Stream[Int] = {
    xs.fold(0, (_ + _))
  }
  
  trait Lazy[A] {
    def extract: A
    def map[B](f: A=>B): Lazy[B] = {
      val self = this
      new Lazy[B] {
        def extract: B = f(self.extract)
      }
    }
    def flatMap[B](f: A=>Lazy[B]): Lazy[B] = {
      val self = this
      new Lazy[B] {
        def extract: B = f(self.extract).extract
      }
    }
  }

  def main(args: Array[String]): Unit = {
     val ones = always(1)
     val twos = always(2)
     val threes = for {
       one <- ones
       two <- twos
     } yield one + two
     for { x <- take(threes, 20) } println(x)
     for { x <- take(sum(always(1)), 20) } println(x)
     var future: Event[Unit] = delay(2000, () => println("Done"))
     tick()
     while  (future match {
       case Later(next) => { future = next.extract; true }
       case _ => false
     }) {
        tick()
     }
  }
}

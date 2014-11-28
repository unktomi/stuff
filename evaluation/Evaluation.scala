package evaluation
/**
 * Created by christopheroliver on 11/22/14.
 */

import java.io.{File, IOException, FileInputStream}

import Evaluation._

// A IMPLIES B = (NOT A) OR B
trait LazilyImplies[A, B] extends (NOT[A] OR B) {
  def *[C](xs: LazilyImplies[B, C]): LazilyImplies[A, C] = compose(xs)
  def compose[C](xs: LazilyImplies[B, C]): LazilyImplies[A, C] = {
    val self = this
    new LazilyImplies[A, C] {
      override def apply(f: (NOT[A]) => Nothing, g: (C) => Nothing): Nothing = {
        self.apply(f, (x:B)=> {
          xs.apply((k)=>k.apply(x), g)
        })
      }
    }
  }
}


// A IMPLIES B = NOT (A AND NOT B)
trait StrictlyImplies[A, B] extends NOT[A AND NOT[B]] {
  def *[C](xs: StrictlyImplies[B, C]): StrictlyImplies[A, C] = compose(xs)
  def compose[C](f: StrictlyImplies[B, C]): StrictlyImplies[A, C] = {
    val self = this
    new StrictlyImplies[A, C] {
      override def apply(xs: A AND NOT[C]): Nothing = {
        xs.apply((x: A, k0: NOT[C]) => {
          self.apply(new (A AND NOT[B]) {
            override def apply(k1: (A, NOT[B]) => Nothing): Nothing = {
              k1(x, new NOT[B] {
                override def apply(y: B): Nothing = {
                  f.apply(new (B AND NOT[C]) {
                    override def apply(k2: (B, NOT[C]) => Nothing): Nothing = {
                      k2(y, k0)
                    }
                  })
                }
              })
            }
          })
        })
      }
    }
  }
}

object Evaluation {
  // A => (A=>B) => B
  def eval[A, B](x: A, f: A=>B): B = f(x)

  // B => (B => A) => A
  def coeval[B, A](y: B): ((B=>A)=>A) = {
    (k)=>k(y)
  }

  def curry[A, B, C](f: (A, B)=>C): A=>(B=>C) = {
    (x: A) => (y: B)=> f(x, y)
  }

  def cocurry[A <: Exception, B, C] (f: C => A + B): (C - B) => A = {
    (x: C - B) => {
      try {
        x.apply((x:C, k: NOT[B])=> f(x).apply((v1: A)=> throw v1, (v2: B)=> k(v2)))
      } catch {
        case r: A => r
      }
    }
  }

  def openFile(file: java.io.File): IOException + FileInputStream = {
    new (IOException + FileInputStream) {
      override def apply(v2: (IOException) => Nothing, v1: (FileInputStream) => Nothing): Nothing = {
        try {
          v1(new FileInputStream(file))
        } catch {
          case e: IOException => v2(e)
        }
      }
    }
  }
  def t {
    val k = cocurry(openFile(_:File))
    val e = k.apply(new (File - FileInputStream) {
      override def apply(v1: (File, NOT[FileInputStream]) => Nothing): Nothing = {
          v1(new File("."), new NOT[FileInputStream] {
            override def apply(v1: FileInputStream): Nothing = {
              println("Opened "+v1)
              sys.exit()
            }
          })
      }
    })
    println(e)
  }

  def apply[A, B, C](f: B => C, x: B) = f(x)

  def coapply[B, C](x: C): (C - B) + B = {
    new ((C - B) + B) {
      override def apply(k1: NOT[(C - B)], k2: NOT[B]): Nothing = {
         k1(new (C - B) {
           override def apply(k3: (C, NOT[B]) => Nothing): Nothing = {
             k3(x, k2)
           }
         })
      }
    }
  }

  type +[A, B] = OR[A, B]
  type -[A, B] = A AND NOT[B]

  type NOT[A] = A => Nothing
  type OR[A, B] = (A => Nothing, B => Nothing) => Nothing
  type AND[A, B] = ((A, B) => Nothing) => Nothing
  type Zero[A] = Nothing => A
  type One[A] = A => Unit

  def lazily[A, B](f: A=>B) = new LazilyImplies[A, B] {
    override def apply(k1: (NOT[A]) => Nothing, k2: (B) => Nothing): Nothing = {
      k1(new NOT[A] {
        override def apply(x: A): Nothing = k2(f(x))
      })
    }
  }

  def strictly[A, B](f: A=>B) = new StrictlyImplies[A, B] {
    override def apply(xs: A AND NOT[B]) = {
      xs.apply((x: A, k: NOT[B])=> {
        k.apply(f(x))
      })
    }
  }

  def main(argv: Array[String]): Unit = {

    def laz = {
      val f = lazily[String, String](_.toUpperCase)
      val g = lazily[String, String](_.concat("world"))
      val q = f * f * g
      q.apply((n: NOT[String]) => n.apply("hello"), (x: String) => {
        println(x)
        sys.exit()
      })
    }

    def stric = {
      val f = strictly[String, String](_.toUpperCase)
      val g = strictly[String, String](_.concat("world"))
      val q = f * g
      q.apply(new (String AND NOT[String]) {
        override def apply(k: (String, NOT[String]) => Nothing): Nothing = {
          k("Hello", new NOT[String] {
            override def apply(x: String): Nothing = {
              println(x)
              sys.exit()
            }
          })
        }
      })
    }
    t
    laz
    stric
  }

}

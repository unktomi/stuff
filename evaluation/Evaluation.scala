package evaluation
/**
 * Created by christopheroliver on 11/22/14.
 */

import java.io.{File, IOException, FileInputStream}

import Evaluation._


import scala.collection.mutable
import scala.collection.mutable.ListBuffer

trait ISO[A, B] {
  def fw(x: A): B
  def bw(y: B): A
}

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
  
  type NOT[A] = A => Nothing
  type OR[A, B] = (A => Nothing, B => Nothing) => Nothing
  type AND[A, B] = ((A, B) => Nothing) => Nothing
  
  type +[A, B] = A OR B
  type ×[A, B] = A AND B

  // Lazy Exponential
  type ~>[A, B] = LazilyImplies[A, B]
  // Strict Exponential
  type ->[A, B] = StrictlyImplies[A, B]

  // Strict Coexponential
  type /=>[A, B] = A AND NOT[B]
  // Lazy Coexponential
  type WITHOUT[A, B] = NOT[NOT[A] OR B]
  type /~>[A, B] = WITHOUT[A, B]

  trait Always[A] extends (A AND Always[A]) {

    def map[B](f: A=>B): Always[B] = {
      lazymap(lazily(f))
    }

    def lazymap[B](f: A ~> B): Always[B] = {
      val self = this
      new Always[B] {
        override def apply(v1: (B, Always[B]) => Nothing): Nothing = {
          self.apply((x, y)=>f.apply((k1)=>k1(x), (v:B)=>v1(v, y.lazymap(f))))
        }
      }
    }

    def extract (k: NOT[A]): Nothing =  {
        apply((x, y) => k(x))
    }

    def flatMap[B](f: A=>Always[B]): Always[B] = {
      lazyflatMap(lazily(f))
    }

    def lazyflatMap[B](f: A ~> Always[B]): Always[B] = {
      val self = this
      new Always[B] {
        override def apply(v1: (B, Always[B]) => Nothing): Nothing = {
          self.apply((x, y)=>f.apply((k1)=>k1(x), (v:Always[B])=> v.extract((x)=>v1(x, y.lazyflatMap(f)))))
        }
      }
    }

    def fold[B](z: B, f: (B AND A) ~> B): Always[B] = {
      val self = this
      new Always[B] {
        override def apply(v1: (B, Always[B]) => Nothing): Nothing = {
          self.apply(
            (x: A, y: Always[A])=>f.apply((k1)=>k1.apply(new (B AND A) {
              override def apply(k: (B, A) => Nothing): Nothing = {
                k(z, x)
              }
            }),
            (v: B)=> {
                v1(v,y.fold(v, f))
             }))
        }
      }
    }

    def take(n: Int): List[A] = {
      var i = 0
      var list = new ListBuffer[A]
      def doit(x: A, y: Always[A]): Unit = {
        if (i == n) {
          throw new Return(list.toList)
        }
        i = i + 1
        list += x
        y.apply((a, b)=> { doit(a, b); ??? })
      }
      try {
          apply((x, y)=> { doit(x, y); ??? })
      } catch {
        case r: Return[List[A]] => r.result
      }
    }

    def drop(n: Int): Always[A] = {
      def doit(i: Int, x: A, y: Always[A]): Unit = {
        if (i == n) {
          throw new Return(y)
        }
        y.apply((a, b)=> { doit(i+1, a, b); ??? })
      }
      try {
        apply((x, y)=> { doit(0, x, y); ??? })
      } catch {
        case r: Return[Always[A]] => r.result
      }
    }

    override def toString: String = {
      take(10).toString
    }

    def eventually: Always[Eventually[A]] = {
      val self = this
      new Always[Eventually[A]] {
        override def apply(v1: (Eventually[A], Always[Eventually[A]]) => Nothing): Nothing = {
           self.apply((x, y)=> {
             v1(now(x), y.eventually)
           })
        }
      }
    }
  }

  def repeat[A](x: A): Always[A] = new Always[A] {
    override def apply(v1: (A, Always[A]) => Nothing): Nothing = {
      v1(x, this)
    }
  }

  trait Eventually[A] extends (A OR Eventually[A]) {
    def map[B](f: A~>B): Eventually[B] = {
      val self = this
      new Eventually[B] {
        override def apply(v1: (B) => Nothing, v2: (Eventually[B]) => Nothing): Nothing = {
          self.apply(
            (x: A)=> {
              f.apply((k)=>k(x), (v: B)=>v1(v))
            },
            (xs: Eventually[A])=> v2(xs.map(f)))
        }
      }
    }
    def flatMap[B](f: A~>Eventually[B]): Eventually[B] = {
      val self = this
      new Eventually[B] {
        override def apply(v1: (B) => Nothing, v2: (Eventually[B]) => Nothing): Nothing = {
          self.apply(
            (x: A)=> {
              f.apply((k)=>k(x), (v: Eventually[B])=>v2(v))
            },
            (xs: Eventually[A])=> v2(xs.flatMap(f)))
        }
      }
    }
  }
  /*
  trait Future[A, Exception] extends (A OR Exception) {
    override def apply(v1: (A) => Nothing, v2: (Exception) => Nothing): Nothing
    def map[B](f: A=>B): Future[B, Exception] = {
      val self = this
      new Future[B, Exception] {
        override def apply(v1: (B) => Nothing, v2: (Exception) => Nothing): Nothing = {
           self.apply((x:A)=>v1(f(x)), (y:Exception)=>v2(y))
        }
      }
    }
    def lazymap[B](f: A~>B): Future[B, Exception] = {
      val self = this
      new Future[B, Exception] {
        override def apply(v1: (B) => Nothing, v2: (Exception) => Nothing): Nothing = {
          self.apply((x:A)=>f.apply((k: NOT[A])=>k(x),
            (v:B)=>v1(v)), (y:Exception)=>v2(y))
        }
      }
    }
  }

  */


  def now[A](x: A): Eventually[A] = new Eventually[A] {
    override def apply(v1: (A) => Nothing, v2: (Eventually[A]) => Nothing): Nothing = {
      v1(x)
    }
  }

  case class Return[A](result: A) extends Exception
  
  // A => (A=>B) => B
  def eval[A, B](x: A, f: A=>B): B = f(x)
  
  def eval[A, B](x: A, f: A~>B, k: B=>Nothing): Nothing = {
    f.apply((k1: NOT[A])=>k1(x), k)
  }

  // B => (B => A) => A
  def coeval[B, A](y: B): ((B=>A)=>A) = {
    (k)=>k(y)
  }

  def curry[A, B, C](f: (A, B) => C): A => (B => C) = {
    (x: A) => (y: B) => f(x, y)
  }

  def uncurry[A, B, C](f: A => (B => C)): (A, B) => C = {
    (x: A, y: B)=> f(x)(y)
  }

  def cocurry[A, B, C] (f: C => A + B): (C /=> B) => A = {
    (c: C /=> B) => {
      try {
        c.apply((x: C, k: NOT[B])=> f(x).apply((v1: A)=> throw Return(v1), (v2: B)=> k(v2)))
      } catch {
        case r: Return[A] => r.result
      }
    }
  }

  def uncocurry[A, B, C](k: (C /=> B) => A): C => (A + B) = {
     new (C => A + B) {
       override def apply(x: C): A + B = {
         new (A + B) {
           override def apply(k1: (A) => Nothing, k2: (B) => Nothing): Nothing = {
             val a = k.apply(new (C /=> B) {
               override def apply(k: (C, NOT[B]) => Nothing): Nothing = {
                 k(x, k2)
               }
             })
             k1(a)
           }
         }
       }
     }
  }
  
  // Distributive Law
  case class Dist[A, B, C]() extends ISO[A AND (B OR C), (A AND B) OR (A AND C)] {

    def fw(xs: A AND (B OR C)): (A AND B) OR (A AND C) = {
      new ((A AND B) OR (A AND C)) {
        override def apply(k1: (A AND B) => Nothing, k2: (A AND C) => Nothing): Nothing = {
          xs.apply((x: A, y: B OR C) =>
            y.apply(
              (b: B) => k1.apply(new (A AND B) {
                override def apply(k: (A, B) => Nothing): Nothing = {
                  k(x, b)
                }
              }),
              (c: C) => k2.apply(new (A AND C) {
                override def apply(k: (A, C) => Nothing): Nothing = {
                  k(x, c)
                }
              })))
        }
      }
    }

    override def bw(y: (A AND B) OR (A AND C)): A AND (B OR C) = {
      new (A AND (B OR C)) {
        override def apply(k: (A, B OR C) => Nothing): Nothing = {
          y.apply(
            (v1: A AND B)=> v1.apply((x: A, y: B)=>k(x, new (B OR C) {
              override def apply(k1: (B) => Nothing, k2: (C) => Nothing): Nothing = {
                k1(y)
              }
            })),
            (v2: A AND C)=> v2.apply((x: A, y: C)=>k(x, new (B OR C) {
              override def apply(k1: (B) => Nothing, k2: (C) => Nothing): Nothing = {
                k2(y)
              }
            })))
        }
      }
    }
  }

  // Co-Distributive Law
  case class CoDist[A, B, C]() extends ISO[ A OR (B AND C), (A OR B) AND (A OR C)] {
    override def fw(xs: A OR (B AND C)): (A OR B) AND (A OR C) = {
      new ((A OR B) AND (A OR C)) {
        override def apply(f: (A OR B, A OR C) => Nothing): Nothing = {
          f(
            new (A OR B) {
              override def apply(k1: (A) => Nothing, k2: (B) => Nothing): Nothing = {
                xs.apply(k1, (bc: B AND C)=> bc.apply((b, c)=> k2(b)))
              }
            },
            new (A OR C) {
              override def apply(k1: (A) => Nothing, k2: (C) => Nothing): Nothing = {
                xs.apply(k1, (bc: B AND C)=> bc.apply((b, c)=> k2(c)))
              }
            })
        }
      }
    }

    override def bw(y: (A OR B) AND (A OR C)): A OR (B AND C) = {
      new (A OR (B AND C)) {
        override def apply(k1: (A) => Nothing, k2: (B AND C) => Nothing): Nothing = {
          y.apply((x: A OR B, y: A OR C) => {
            x.apply(k1, (u: B)=> y.apply(k1, (v: C)=> k2.apply(new (B AND C) {
              override def apply(k: (B, C) => Nothing): Nothing = {
                k(u, v)
              }
            })))
          })
        }
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

  def apply[B, C](f: B => C, x: B): C = f(x)

  def coapply[B, C](x: C): (C /=> B) + B = {
    new ((C /=> B) + B) {
      override def apply(k1: NOT[(C /=> B)], k2: NOT[B]): Nothing = {
         k1(new (C /=> B) {
           override def apply(k3: (C, NOT[B]) => Nothing): Nothing = {
             k3(x, k2)
           }
         })
      }
    }
  }

  def lazyCoapply[B, C](x: C): (C WITHOUT B) OR B = {
    new ((C WITHOUT B) + B) {
      override def apply(k1: (C WITHOUT B) => Nothing, k2: (B) => Nothing): Nothing = {
        k1(new (C WITHOUT B) {
          override def apply(k3: NOT[C] OR B): Nothing = {
             k3.apply((k1: NOT[C])=> k1.apply(x), k2)
          }
        })
      }
    }
  }

  def lazyCocurry[A, B, C] (f: C => A OR B): (C WITHOUT B) => A = {
    (x: C WITHOUT B) => {
      try {
        x.apply(new (NOT[C] OR B) {
          override def apply(k1: (NOT[C]) => Nothing, k2: (B) => Nothing): Nothing = {
            k1(new NOT[C] {
              override def apply(v1: C): Nothing = {
                f(v1).apply((x: A) => throw Return(x), k2)
              }
            })
          }
        })
      } catch {
        case r: Return[A] => r.result
      }
    }
  }


  implicit def lazily[A, B, C](f: (A, B)=>C): (A AND B) ~> C = {
      new ((A AND B) ~> C) {
        override def apply(v1: (NOT[A AND B]) => Nothing, v2: (C) => Nothing): Nothing = {
           v1.apply(new NOT[A AND B] {
             override def apply(v1: A AND B): Nothing = {
                v1.apply((x, y)=>v2(f(x, y)))
             }
           })
        }
      }
  }

  implicit def lazily[A, B](f: A=>B) = new LazilyImplies[A, B] {
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

  def end(): Nothing = throw Return(())

  def main(argv: Array[String]): Unit = {
    
    def t {
      val k = cocurry(openFile(_:File))
      val i = uncocurry(k)
      val e = k.apply(new (File /=> FileInputStream) {
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
      val j = i.apply(new File("."))
      j.apply((ex)=>{
        println(ex)
        sys.exit()
      }, (strm)=> {
        println(strm)
        sys.exit()
      })
    }
    
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
    val s = repeat(0)
    val m = s.map((x:Int) => x + 1)
    println(m)
    val q = for {
      j <- m
    } yield j + 1
    println(q)

    val n = m.fold(0, (x: Int, y:Int)=> x + y)

    println(n)
    t
    laz
    stric
  }

}

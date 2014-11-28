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

  def uncurry[A, B, C](f: A=>(B=>C)): (A, B)=>C = {
    (x: A, y: B)=> f(x)(y)
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

  def uncocurry[A <: Exception, B, C](k: (C - B) => A): C => (A + B) = {
     new (C => A + B) {
       override def apply(x: C): A + B = {
         new (A + B) {
           override def apply(v1: (A) => Nothing, v2: (B) => Nothing): Nothing = {
             val a = k.apply(new (C - B) {
               override def apply(k: (C, NOT[B]) => Nothing): Nothing = {
                 k(x, v2)
               }
             })
             v1(a)
           }
         }
       }
     }
  }

  def dist[A, B, C](xs: A AND (B OR C)): (A AND B) OR (A AND C) = {
    new ((A AND B) OR (A AND C)) {
      override def apply(v1: (A AND B) => Nothing, v2: (A AND C) => Nothing): Nothing = {
        xs.apply((x: A, y: B OR C)=>
          y.apply((b: B)=> v1.apply(new (A AND B) {
            override def apply(k: (A, B) => Nothing): Nothing = {
              k(x, b)
            }
          }),
            (c)=> v2.apply(new (A AND C) {
              override def apply(k: (A, C) => Nothing): Nothing = {
                k(x, c)
              }
            })))
      }
    }
  }

  def codist[A, B, C](xs: A OR (B AND C)): (A OR B) AND (A OR C) = {
    new ((A OR B) AND (A OR C)) {
      override def apply(f: (A OR B, A OR C) => Nothing): Nothing = {
         f(new (A OR B) {
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
    val i = uncocurry(k)
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
    val j = i.apply(new File("."))
    j.apply((ex)=>{
      println(ex)
      sys.exit()
    }, (strm)=> {
      println(strm)
      sys.exit()
    })
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

  def lazyCocurry[A <: Exception, B, C] (f: C => A OR B): (C WITHOUT B) => A = {
    (x: C WITHOUT B) => {
      try {
        x.apply(new (NOT[C] OR B) {
          override def apply(k1: (NOT[C]) => Nothing, k2: (B) => Nothing): Nothing = {
            k1(new NOT[C] {
              override def apply(v1: C): Nothing = {
                f(v1).apply((x: A) => throw x, k2)
              }
            })
          }
        })
      } catch {
        case r: A => r
      }
    }
  }

  type NOT[A] = A => Nothing
  type OR[A, B] = (A => Nothing, B => Nothing) => Nothing
  type AND[A, B] = ((A, B) => Nothing) => Nothing
  type Zero[A] = Nothing => A
  type One[A] = A => Unit
  type +[A, B] = A OR B
  type -[A, B] = A AND NOT[B]

  type WITHOUT[A, B] = NOT[NOT[A] OR B]

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

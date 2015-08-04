package evaluation
/**
 * Created by christopheroliver on 11/22/14.
 */

import java.io.{File, IOException, FileInputStream}

import Evaluation._
import scala.collection.mutable.ListBuffer



// A IMPLIES B = (NOT A) OR B
trait LazilyImplies[A, B] extends (NOT[A] OR B) {

  override def apply(v1: (NOT[A]) => Nothing, v2: (B) => Nothing): Nothing

  // composition
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
  // as strict
  def strictly: StrictlyImplies[A, B] = {
    val self = this
    new StrictlyImplies[A, B] {
      override def apply(v1: AND[A, NOT[B]]): Nothing = {
        v1.apply((u: A, v: NOT[B]) => self.apply((f: NOT[A]) => f(u), (g: B) => v(g)))
      }
    }
  }
}

// A IMPLIES B = NOT (A AND NOT B)
trait StrictlyImplies[A, B] extends NOT[A AND NOT[B]] {

  override def apply(v1: A AND NOT[B]): Nothing

  // composition
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

  // as lazy
  def lazily: LazilyImplies[A, B] = {
    val self = this
    new LazilyImplies[A, B] {
      override def apply(v1: (NOT[A]) => Nothing, v2: (B) => Nothing): Nothing = {
        v1(new NOT[A] {
          override def apply(v1: A): Nothing = {
            self.apply(new (A AND NOT[B]) {
              override def apply(k: (A, NOT[B]) => Nothing): Nothing = {
                k(v1, v2)
              }
            })
          }
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

  type LENS[A, B] = (A ~> B) AND ((A AND B) ~> A)
  type /[A, B] = LENS[A, B]

  type PRISM[E, A] = (A ~> E) AND (E ~> (A OR E))
  type -[A, B] = PRISM[A, B]


  case class ID1[A]() extends ISO[A - Nothing, NOT[NOT[A]]] {
    override def bw(y: NOT[NOT[A]]): A - Nothing = {
      new (A - Nothing) {

        override def toString(): String = {
          try {
            apply((j, k) => j.apply((nothing) => ???, (v: A) => throw Return(v)))
          } catch {
            case ret:Return[A] => ret.result.toString
          }
        }

        override def apply(v1: (~>[Nothing, A], ~>[A, OR[Nothing, A]]) => Nothing): Nothing = {
          y.apply((x: A) => {
            v1.apply(new (Nothing ~> A) {
              override def apply(v1: (NOT[Nothing]) => Nothing, v2: (A) => Nothing): Nothing = {
                v2(x)
              }
            },
              new (A ~> (Nothing + A)) {
                override def apply(ignored: (NOT[A]) => Nothing, v2: (+[Nothing, A]) => Nothing): Nothing = {
                  v2(new (Nothing + A) {
                    override def apply(ignored: (Nothing) => Nothing, k2: (A) => Nothing): Nothing = {
                      k2(x)
                    }
                  })
                }
              })
          })
        }
      }
    }

    override def fw(x: A - Nothing): NOT[NOT[A]] = {
      (ret: NOT[A])=> {
        x.apply((_, k: A ~> (Nothing + A)) => k.apply((k1: NOT[A])=> ???,
                                  (k2: Nothing + A)=> k2.apply((nothing: Nothing)=> nothing, (v: A)=> ret(v))))
      }
    }
  }

  case class ID2[A, B]() extends ISO[(A + B) - B, A - Nothing] {
    override def bw(y: A - Nothing): (A + B) - B = {
      new ((A + B) - B) {

        override def apply(v1: (~>[B, +[A, B]], ~>[+[A, B], OR[B, +[A, B]]]) => Nothing): Nothing = {

        //override def apply(v1: (B ~> (A + B), (A + B) ~> B + (A + B)) => Nothing): Nothing = {
          v1.apply(new (B ~> (A + B)) {
            override def apply(v1: (NOT[B]) => Nothing, v2: (A + B) => Nothing): Nothing = {
               y.apply((j: Nothing ~> A, k) => k.apply((s: NOT[A])=> ???, (t: Nothing + A)=> t.apply((nothing)=> nothing, (x:A)=>v2(new (A + B) {
                 override def apply(v1: (A) => Nothing, v2: (B) => Nothing): Nothing = {
                   v1(x)
                 }
               }))) )
            }
          },
          new ~>[+[A, B], OR[B, +[A, B]]] {
            override def apply(v1: (NOT[+[A, B]]) => Nothing, v2: (OR[B, +[A, B]]) => Nothing): Nothing = {
              v1((k)=> {
                 ///k.apply((x: A)=> y.apply((j: Nothing ~> A, k1) => k1), (y: B)=> ???)
                ???
              })
            }

          })
        }
      }
    }

    override def fw(x: (A + B) - B): A - Nothing = {
        ???
    }
  }

  def just[A](x: A): A - Nothing = {
     new (A - Nothing) {
       override def apply(v1: (~>[Nothing, A], ~>[A, OR[Nothing, A]]) => Nothing): Nothing = {
         v1(new (Nothing ~> A) {
           override def apply(v1: (NOT[Nothing]) => Nothing, v2: (A) => Nothing): Nothing = {
             v2(x)
           }
         },
         new (A ~> (Nothing + A)) {
           override def apply(v1: (NOT[A]) => Nothing, v2: (+[Nothing, A]) => Nothing): Nothing = {
             v2(new (Nothing + A) {
               override def apply(v1: (Nothing) => Nothing, v2: (A) => Nothing): Nothing = {
                 v2(x)
               }
             })
           }
         })
       }
     }
  }

  def doublyNegate[A](x: A): NOT[NOT[A]] = {
    (k: NOT[A]) => k(x)
  }

  // Lazy Exponential
  type ~>[A, B] = LazilyImplies[A, B]
  // Strict Exponential
  type ->[A, B] = StrictlyImplies[A, B]

  // Strict Coexponential
  type /->[A, B] = A AND NOT[B]
  // Lazy Coexponential
  type WITHOUT[A, B] = NOT[NOT[A] OR B]
  type /~>[A, B] = A WITHOUT B

  // Sabin's Intersection and Union types:

  // Intersection
  type and[T, U] = T with U

  type Cont[T] = NOT[NOT[T]]

  // Union
  type or[T, U] = { type selection[X] = Cont[X] <:<  NOT[NOT[T] with NOT[U]] }

  trait NaturalTransformation[F[_], G[_]] {
    def apply[A](f: F[A]): G[A]
  }

  type ==>[F[_], G[_]] = NaturalTransformation[F, G]

  implicit def polyToMono[F[_], G[_], T](f : F ==> G) : F[T] => G[T] = f(_)

  type Const[C] = {
    type apply[T] = C
  }

  val j: Int = 1
  val k: Const[Int]#apply[Int] = j

  val rev = new (List ==> List) {
    override def apply[A](f: List[A]): List[A] = {
      f.reverse
    }
  }

  def listApp[A](xs: List[A], f: List[A] => List[A]): List[A] = f(xs)

  val q = listApp(List(1, 2), polyToMono[List, List, Int](rev))

  trait Existential[T[_], A] {
      def apply[B](k: T[A]=>B): B
  }


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

    def zip[B, C](xs: Always[B], f: (A, B) => C): Always[C] = {
      val self = this
      new Always[C] {
        override def apply(v1: (C, Always[C]) => Nothing): Nothing = {
          self.apply((y, ys)=> xs.apply((z, zs)=> v1(f(y, z), ys.zip(zs, f))))
        }
      }
    }

    def zip[B, C](xs: Always[B], f: (A AND B) ~> C): Always[C] = {
      val self = this
      new Always[C] {
        override def apply(v1: (C, Always[C]) => Nothing): Nothing = {
          self.apply((y, ys)=> xs.apply((z, zs)=> f.apply((k1)=>k1.apply(new (A AND B) {
            override def apply(k: (A, B) => Nothing): Nothing = {
              k(y, z)
            }
          }),
            (v: C)=> {
              v1(v, ys.zip(zs, f))
            })))
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
                v1(v, y.fold(v, f))
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
  }

  case class ISOLazyStrict[A, B]() extends  ISO[LazilyImplies[A, B], StrictlyImplies[A, B]] {
    override def fw(x: LazilyImplies[A, B]): StrictlyImplies[A, B] = {
      new StrictlyImplies[A, B] {
        override def apply(v1: A AND NOT[B]): Nothing = {
          v1.apply((u: A, f: NOT[B])=> x.apply((g: NOT[A])=> g(u), (v: B)=> f(v)))
        }
      }
    }

    override def bw(y: StrictlyImplies[A, B]): LazilyImplies[A, B] = {
      new LazilyImplies[A, B] {
        override def apply(v1: (NOT[A]) => Nothing, v2: (B) => Nothing): Nothing = {
          v1(new NOT[A] {
            override def apply(x: A): Nothing = {
              y.apply(new (A AND NOT[B]) {
                override def apply(k: (A, NOT[B]) => Nothing): Nothing = {
                  k(x, v2)
                }
              })
            }
          })
        }
      }
    }
  }

  case class T1[A]() extends ISO[Always[A], NOT[Eventually[NOT[A]]]] {

    def f(x: Always[A], v1: Eventually[NOT[A]]): Nothing = {
      v1.apply((k: NOT[A])=> x.apply((y: A, ys: Always[A])=> k(y)), (xs: Eventually[NOT[A]])=> x.apply((y: A, ys: Always[A])=> f(ys, xs) ))
    }

    override def fw(x: Always[A]): NOT[Eventually[NOT[A]]] = new NOT[Eventually[NOT[A]]] {
      override def apply(v1: Eventually[NOT[A]]): Nothing = {
         f(x, v1)
      }
    }

    override def bw(y: NOT[Eventually[NOT[A]]]): Always[A] = new Always[A] {
      override def apply(v1: (A, Always[A]) => Nothing): Nothing = {
        val v: Eventually[NOT[A]] = new Eventually[NOT[A]] {
          override def apply(k1: (NOT[A]) => Nothing, k2: (Eventually[NOT[A]]) => Nothing): Nothing = {
             k1(new NOT[A] {
               override def apply(x: A): Nothing = {
                  v1(x, bw(new NOT[Eventually[NOT[A]]] {
                    override def apply(u: Eventually[NOT[A]]): Nothing = {
                      k2(u)
                    }
                  }))
               }
             })
          }
        }
        y.apply(v)
      }
    }
  }

  case class T2[A]() extends ISO[Eventually[A], NOT[Always[NOT[A]]]] {
    override def fw(e: Eventually[A]): NOT[Always[NOT[A]]] = {
       new NOT[Always[NOT[A]]] {
         override def apply(v1: Always[NOT[A]]): Nothing = {
           e.apply((x: A)=>v1.apply((k, ks)=> k.apply(x)), (e1: Eventually[A])=> fw(e1).apply(v1))
         }
       }
    }

    override def bw(y: NOT[Always[NOT[A]]]): Eventually[A] = {
       new Eventually[A] {
         override def apply(v1: (A) => Nothing, v2: (Eventually[A]) => Nothing): Nothing = {
           y.apply(new Always[NOT[A]] {
             val me: Always[NOT[A]] = this
             override def apply(k: (NOT[A], Always[NOT[A]]) => Nothing): Nothing = {
               k(v1, me)
             }
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

    override def apply(v1: (A) => Nothing, v2: (Eventually[A]) => Nothing): Nothing

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


    override def toString(): String = {
       try {
         apply((x: A) => throw new Return("" + x), (xs: Eventually[A]) => throw Return(xs.toString()))
       } catch {
         case r: Return[String] => r.result
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

  def now[A](x: A): Eventually[A] = new Eventually[A] {
    override def apply(v1: (A) => Nothing, v2: (Eventually[A]) => Nothing): Nothing = {
      v1(x)
    }
  }

  case class Return[A](result: A) extends Exception
  
  // A => (A=>B) => B
  def eval[A, B](x: A, f: A=>B): B = f(x)
  
  def eval[A, B](x: A, f: A~>B, k: NOT[B]): Nothing = {
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

  def cocurry[A, B, C] (f: C => A + B): (C /-> B) => A = {
    (c: C /-> B) => {
      try {
        c.apply((x: C, k: NOT[B])=> f(x).apply((v1: A)=> throw Return(v1), (v2: B)=> k(v2)))
      } catch {
        case r: Return[A] => r.result
      }
    }
  }

  def uncocurry[A, B, C](k: (C /-> B) => A): C => (A + B) = {
     new (C => A + B) {
       override def apply(x: C): A + B = {
         new (A + B) {
           override def apply(k1: (A) => Nothing, k2: (B) => Nothing): Nothing = {
             val a = k.apply(new (C /-> B) {
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
  case class CoDist[A, B, C]() extends ISO[A OR (B AND C), (A OR B) AND (A OR C)] {
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

  def openFile(file: java.io.File): IOException OR FileInputStream = {
    new (IOException OR FileInputStream) {
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

  def coapply[B, C](x: C): (C /-> B) + B = {
    new ((C /-> B) + B) {
      override def apply(k1: NOT[(C /-> B)], k2: NOT[B]): Nothing = {
         k1(new (C /-> B) {
           override def apply(k3: (C, NOT[B]) => Nothing): Nothing = {
             k3(x, k2)
           }
         })
      }
    }
  }

  def lazyCoapply[B, C](x: C): (C WITHOUT B) OR B = {
    new ((C WITHOUT B) OR B) {
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

  def directly[A, B](f: A->B): A=>B = {
    (x: A)=> {
      try {
        f.apply(new (A AND NOT[B]) {
          override def apply(v1: (A, NOT[B]) => Nothing): Nothing = {
            v1(x, new NOT[B] {
              override def apply(v1: B): Nothing = {
                throw Return(v1)
              }
            })
          }
        })
      } catch {
        case r: Return[B] => r.result
      }
    }
  }

  def directly[A, B](f: A~>B): A=>B = {
    (x: A)=> {
      try {
        f.apply((k) => k(x), (y) => throw Return(y))
      } catch {
        case r: Return[B] => r.result
      }
    }
  }

  def end(): Nothing = throw Return(())

  def run(f: ()=> Unit): Unit = {
    try {
        f()
    } catch {
      case Return(())=> ()
    }
  }


  type Lax[A] = Eventually[Always[A]]

  def lax[A](x: A): Lax[A] = now(repeat(x))

  /// (A and eventually always B) implies eventually always (A and B)

  /*

  def transpose[A, B](xs: A AND Lax[B]): Lax[A AND B] = {
    new Lax[A AND B] {
      override def apply(v1: (Always[A AND B]) => Nothing, v2: (Eventually[Always[A AND B]]) => Nothing): Nothing = {
        xs.apply((x: A, y: Lax[B])=> y.apply((s)=> v1(s.map((z: B)=> new (A AND B) {
          override def apply(v1: (A, B) => Nothing): Nothing = {
            v1(x, z)
          }
        })), (y: Eventually[Always[B]])=> y.map(new (Always[B] ~> Always[A AND B]) {
          override def apply(v1: (NOT[Always[B]]) => Nothing, v2: (Always[AND[A, B]]) => Nothing): Nothing = {
              v1(new NOT[Always[B]] {
                override def apply(v1: Always[B]): Nothing = {
                  v2(v1.map((z: B) => {
                    new (A AND B) {
                      override def apply(v1: (A, B) => Nothing): Nothing = {
                        v1(x, z)
                      }
                    }
                  }))
                }
              })
          }
        })))
      }
    }
  }

  */

  def main(argv: Array[String]): Unit = {

    def size[T: (Int or String)#selection](t: T) = {
      t match {
        case i:Int => i
        case j: String => j.length()
      }
    }
    println(size(100))
    println(size("Hello"))

    def t {
      val k = cocurry(openFile(_:File))
      val i = uncocurry(k)
      val e = k.apply(new (File /-> FileInputStream) {
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
      val q = f * g * g
      /*
      q.apply((n: NOT[String]) => n.apply("hello"), (x: String) => {
        println(x)
        sys.exit()
      })
      */
      val d = directly(q)
      println(d("hello"))
    }

    def stric = {
      val f = strictly[String, String](_.toUpperCase)
      val g = strictly[String, String](_.concat("world"))
      val q = f * g * f
      /*
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
      */
      val d = directly(q)
      println(d("Hello"))
    }
    val s = repeat(0)
    val m = s.map((x:Int) => x + 1)
    println(m)
    val q = for {
      j <- m
    } yield j + 1
    println(q)

    //val n = m.fold(0, (x: Int, y:Int)=> x + y)

    //println(n)



    val id1 = ID1[Int]()
    val neg10 = id1.bw(doublyNegate(10))
    println(neg10)


    val t1 = new T1[String]()
    val qs = t1.bw(t1.fw(repeat("Hello")))
    println(qs)

    //t
    laz
    stric

    case class Meal(name: String)

    type Consumer[A] = A => Unit
    type Diner = Consumer[Meal]
    type Stream[A] = Always[A]

    type Restaurant = Consumer[Stream[Diner]]

    val diners: Stream[Diner] = repeat((meal: Meal)=> { println("ate: "+meal) })
    val meals = repeat(Meal("eggs"))
    val res: Restaurant = (diners: Stream[Diner]) =>  {
      diners.zip(meals, (d: Diner, m: Meal)=> d(m)).take(10)
    }
    res(diners)

  }

}

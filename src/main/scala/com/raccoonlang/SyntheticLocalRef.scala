package com.raccoonlang

import com.raccoonlang.CoreAst.LocalRef

import java.util.concurrent.atomic.AtomicInteger

/** Process-wide identity supply for kernel-generated locals; parser/elaborator locals remain non-negative. */
private[raccoonlang] object SyntheticLocalRef {
  private val nextId = new AtomicInteger(-1)

  def fresh(name: String): LocalRef = {
    var allocated = false
    var id = 0
    while (!allocated) {
      id = nextId.get()
      if (id == Int.MinValue)
        throw new IllegalStateException("kernel exhausted synthetic local identifiers")
      allocated = nextId.compareAndSet(id, id - 1)
    }
    LocalRef(id, name)
  }
}

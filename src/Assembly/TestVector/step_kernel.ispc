export void simple_crypto_step(uniform int data[], uniform int key[], uniform int count) {
      foreach (i = 0 ... count) {
          int val = data[i];
          val = val + key[i % 4];
          data[i] = val;
      }
  }
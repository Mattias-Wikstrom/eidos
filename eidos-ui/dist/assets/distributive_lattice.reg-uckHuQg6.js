var e=`/* Theory in regular logic that axiomatizes the concept of a distributive lattice */
{
  subtheories {
    implicit {
      lattice: @lattice
    }
  },
  axioms {
    facts {
      x : D,  y : D,  z : D,  join(x, meet(y, z)) = meet(join(x, y), join(x, z));
      x : D,  y : D,  z : D,  meet(x, join(y, z)) = join(meet(x, y), meet(x, z));   
    }
  }
}`;export{e as default};
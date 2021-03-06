/* -*- mode: C++; c-basic-offset: 2; indent-tabs-mode: nil -*- */
/*
 *  Main authors:
 *     Guido Tack <tack@gecode.org>
 *     Christian Schulte <schulte@gecode.org>
 *
 *  Contributing authors:
 *     Gabor Szokoli <szokoli@gecode.org>
 *
 *  Copyright:
 *     Guido Tack, 2004
 *     Christian Schulte, 2004
 *     Gabor Szokoli, 2004
 *
 *  Last modified:
 *     $Date: 2011-07-13 21:14:41 +0200 (Wed, 13 Jul 2011) $ by $Author: tack $
 *     $Revision: 12200 $
 *
 *  This file is part of Gecode, the generic constraint
 *  development environment:
 *     http://www.gecode.org
 *
 *  Permission is hereby granted, free of charge, to any person obtaining
 *  a copy of this software and associated documentation files (the
 *  "Software"), to deal in the Software without restriction, including
 *  without limitation the rights to use, copy, modify, merge, publish,
 *  distribute, sublicense, and/or sell copies of the Software, and to
 *  permit persons to whom the Software is furnished to do so, subject to
 *  the following conditions:
 *
 *  The above copyright notice and this permission notice shall be
 *  included in all copies or substantial portions of the Software.
 *
 *  THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
 *  EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
 *  MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
 *  NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
 *  LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
 *  OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
 *  WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
 *
 */

namespace Gecode {

  class SetVarArgs;
  class SetVarArray;

  /// Traits of %VarArgArray&lt;%SetVar>
  template<>
  class ArrayTraits<VarArgArray<SetVar> > {
  public:
    typedef SetVarArgs StorageType;
    typedef SetVar     ValueType;
    typedef SetVarArgs ArgsType;
  };

  /// Traits of %VarArray&lt;%SetVar>
  template<>
  class ArrayTraits<VarArray<SetVar> > {
  public:
    typedef SetVarArray  StorageType;
    typedef SetVar       ValueType;
    typedef SetVarArgs   ArgsType;
  };

  /// Traits of %SetVarArray
  template<>
  class ArrayTraits<SetVarArray> {
  public:
    typedef SetVarArray  StorageType;
    typedef SetVar       ValueType;
    typedef SetVarArgs   ArgsType;
  };
  /// Traits of %SetVarArgs
  template<>
  class ArrayTraits<SetVarArgs> {
  public:
    typedef SetVarArgs StorageType;
    typedef SetVar     ValueType;
    typedef SetVarArgs ArgsType;
  };

}

// STATISTICS: set-other

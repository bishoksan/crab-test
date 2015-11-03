#ifndef CRAB_SPARSE_GRAPH_HPP
#define CRAB_SPARSE_GRAPH_HPP
#include <vector>
#include <crab/common/types.hpp>

/* A (slightly) cleaner implementation of a sparse weighted graph.
 * 
 */
namespace ikos {

template <class Weight>
class SparseWtGraph : public writeable {
  public:
    typedef Weight Wt;
    typedef SparseWtGraph<Wt> graph_t;

    typedef unsigned int vert_id;

    SparseWtGraph(unsigned int _maxsz = 10, float _growth_rate = 1.4)
      : max_sz(_maxsz), sz(0), growth_rate(_growth_rate),
        edge_count(0),
        fwd_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        rev_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        mtx((Wt*) malloc(sizeof(Wt)*max_sz*max_sz))
    {
      /*
      for(vert_id v = 0 ; v < sz; v++)
      {
        succs(v).clear(); preds(v).clear();
      }

      check_adjs();
      */
    }

    template<class Wo>
    SparseWtGraph(const SparseWtGraph<Wo>& o)
      : max_sz(o.max_sz), sz(o.sz), growth_rate(o.growth_rate),
        edge_count(0),
        fwd_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        rev_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        mtx((Wt*) malloc(sizeof(Wt)*max_sz*max_sz))
        , is_free(o.is_free), free_id(o.free_id)
    {
      assert(sz <= max_sz);
      for(vert_id v = 0 ; v < sz; v++)
      {
        succs(v).clear(); preds(v).clear();
      }

      for(vert_id v : o.verts())
        for(vert_id d : o.succs(v))
          add_edge(v, o.edge_val(v, d), d);

//      check_adjs();
    }

    SparseWtGraph(const SparseWtGraph<Wt>& o)
      : max_sz(o.max_sz), sz(o.sz), growth_rate(o.growth_rate),
        edge_count(0),
        fwd_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        rev_adjs((unsigned int*) malloc(sizeof(unsigned int)*max_sz*(2*max_sz+1))),
        mtx((Wt*) malloc(sizeof(Wt)*max_sz*max_sz))
        , is_free(o.is_free), free_id(o.free_id)
    {
      assert(sz <= max_sz);
      for(vert_id v = 0 ; v < sz; v++)
      {
        succs(v).clear(); preds(v).clear();
      }

      for(vert_id v : o.verts())
        for(vert_id d : o.succs(v))
          add_edge(v, o.edge_val(v, d), d);

//      check_adjs();
    }

    SparseWtGraph(SparseWtGraph<Wt>&& o)
      : max_sz(o.max_sz), sz(o.sz), growth_rate(o.growth_rate),
        edge_count(o.edge_count),
        fwd_adjs(o.fwd_adjs), rev_adjs(o.rev_adjs), mtx(o.mtx),
        is_free(std::move(o.is_free)), free_id(std::move(o.free_id))
    {
      o.max_sz = 0;
      o.sz = 0;
      o.fwd_adjs = NULL;
      o.rev_adjs = NULL;
      o.mtx = NULL; 
    }

    SparseWtGraph& operator=(const SparseWtGraph<Wt>& o)
    {
      if((&o) == this)
        return *this;  
      
      // Make sure the number of vertices matches,
      // and active adjacency lists are initialized.
      /*
      clear_edges(); 
      growCap(o.sz);
      for(; sz < o.sz; sz++)
      {
        // Initialize extra adj_lists
        succs(sz).clear();
        preds(sz).clear();
      }
      sz = o.sz;
      */
      clear();
      growTo(o.sz);

      // Now copy the edges
      for(vert_id s : o.verts())
      {
        for(vert_id d : o.succs(s))
        {
          add_edge(s, o.edge_val(s, d), d);
        }
      }

      // Copy the free vertices
      free_id = o.free_id;
      is_free = o.is_free;

//      check_adjs();

      return *this;
    }

    SparseWtGraph& operator=(SparseWtGraph<Wt>&& o)
    {
      if(max_sz > 0)
      {
        free(mtx);
        free(fwd_adjs);
        free(rev_adjs);
      }

      max_sz = o.max_sz;
      sz = o.sz;
      growth_rate = o.growth_rate;
      edge_count = o.edge_count;
      fwd_adjs = o.fwd_adjs;
      rev_adjs = o.rev_adjs;
      mtx = o.mtx;
      is_free = std::move(o.is_free);
      free_id = std::move(o.free_id);

      o.max_sz = 0;
      o.sz = 0;
      o.fwd_adjs = NULL;
      o.rev_adjs = NULL;
      o.mtx = NULL; 
      
      return *this;
    }

    void check_adjs(void)
    {
      for(vert_id v : verts())
      {
        assert(succs(v).size() <= sz);
        for(vert_id s : succs(v))
        {
          assert(s < sz);
          assert(preds(s).mem(v));
        }

        assert(preds(v).size() <= sz);
        for(vert_id p : preds(v))
        {
          assert(p < sz);
          assert(succs(p).mem(v));
        }
      }
    }

    ~SparseWtGraph()
    {
      if(max_sz > 0)
      {
        for(vert_id v = 0; v < sz; v++)
        {
          for(vert_id d : succs(v))
            (&(mtx[max_sz*v + d]))->~Wt();
        }
        free(mtx);
        free(fwd_adjs);
        free(rev_adjs);
      }
    }

    template<class G> 
    static graph_t copy(G& g)
    {
      graph_t ret;
      ret.growTo(g.size());

      for(vert_id s : g.verts())
      {
        for(vert_id d : g.succs(s))
        {
          ret.add_edge(s, g.edge_val(s, d), d);
        }
      }
      // Unforunately, views don't have
      // convenient 'is_free' arrays.
//      ret.free_id = g.free_id;
//      ret.is_free = g.is_free;
//      ret.check_adjs();

      return ret;
    }

    bool is_empty(void) const { return edge_count == 0; }

    vert_id new_vertex(void)
    {
      vert_id v;
      if(free_id.size() > 0)
      {
        v = free_id.back();
        assert(v < sz);
        free_id.pop_back();
        is_free[v] = false;
      } else {
        if(max_sz <= sz)
        {
          // Make sure max_sz is strictly increasing
          growCap(1 + max_sz*growth_rate);
        }
        assert(sz < max_sz);
        v = sz++;
        is_free.push_back(false);
      }
      preds(v).clear();
      succs(v).clear();

      return v;
    }

    void forget(vert_id v)
    {
      assert(v < sz);
      // FIXME: currently assumes v is not free
      if(is_free[v])
        return;

      free_id.push_back(v); 
      is_free[v] = true;
      
      // Remove (s -> v) from preds.
      edge_count -= succs(v).size();
      for(vert_id s : succs(v))
      {
        (&(mtx[max_sz*v + s]))->~Wt();
        preds(s).remove(v);
      }
      succs(v).clear();

      // Remove (v -> p) from succs
      edge_count -= preds(v).size();
      for(vert_id p : preds(v))
      {
        (&(mtx[max_sz*p + v]))->~Wt();
        succs(p).remove(v); 
      }
      preds(v).clear();
    }

    // Check whether an edge is live
    bool elem(vert_id x, vert_id y) {
      return succs(x).mem(y);
    }

    Wt& edge_val(vert_id x, vert_id y) const {
      return mtx[max_sz*x + y];
    }

    // Precondition: elem(x, y) is true.
    Wt operator()(vert_id x, vert_id y) const {
      return mtx[max_sz*x + y];
    }

    void clear_edges(void) {
      for(vert_id v : verts())
      {
        // Make sure the matrix entries are destructed
        for(vert_id d : succs(v))
          (&(mtx[max_sz*v + d]))->~Wt();

        preds(v).clear();
        succs(v).clear();
      }
      edge_count = 0;
    }

    void clear(void)
    {
      clear_edges();
      is_free.clear();
      free_id.clear();
      sz = 0;
    }

    // Number of allocated vertices
    int size(void) const {
      return sz;
    }

    // Assumption: (x, y) not in mtx
    void add_edge(vert_id x, Wt wt, vert_id y)
    {
//      assert(x < size() && y < size());
//      assert(x != y);
//      assert(!elem(x, y));
      succs(x).add(y);
      preds(y).add(x);
      // Allocate a new Wt at the given offset.
      new (&(mtx[x*max_sz + y])) Wt(wt);
      edge_count++;
    }

    void set_edge(vert_id s, Wt w, vert_id d)
    {
//      assert(s < size() && d < size());
      if(!elem(s, d))
        add_edge(s, w, d);
      else
        edge_val(s, d) = w;
    }

    template<class Op>
    void update_edge(vert_id s, Wt w, vert_id d, Op& op)
    {
      if(elem(s, d))
      {
        edge_val(s, d) = op.apply(edge_val(s, d), w);
        return;
      }

      if(!op.default_is_absorbing())
        add_edge(s, w, d);
    }

    class vert_iterator {
    public:
      vert_iterator(vert_id _v, const vector<bool>& _is_free)
        : v(_v), is_free(_is_free)
      { }
      vert_id operator*(void) const { return v; }
      vert_iterator& operator++(void) { ++v; return *this; }
      vert_iterator& operator--(void) { --v; return *this; }
      bool operator!=(const vert_iterator& o) {
        while(v < o.v && is_free[v])
          ++v;
        return v < o.v;
      }
    protected:
      vert_id v;
      const vector<bool>& is_free;
    };
    class vert_range {
    public:
      vert_range(vert_id _sz, const vector<bool>& _is_free)
        : sz(_sz), is_free(_is_free)
      { }
      vert_iterator begin(void) const { return vert_iterator(0, is_free); } 
      vert_iterator end(void) const { return vert_iterator(sz, is_free); }
      // unsigned int size(void) const { return (unsigned int) sz; }
    protected:
      vert_id sz; 
      const vector<bool>& is_free;
    };
    // FIXME: Verts currently iterates over free vertices,
    // as well as existing ones
    vert_range verts(void) const { return vert_range(sz, is_free); }

    typedef vert_id* adj_iterator;
    typedef adj_iterator succ_iterator;
    typedef adj_iterator pred_iterator;
    class adj_list {
    public:
      typedef adj_iterator iterator;

      adj_list(unsigned int* _ptr, unsigned int max_sz)
        : ptr(_ptr), sparseptr(_ptr+1+max_sz)
      { }
      vert_id* begin(void) const { return (vert_id*) (ptr+1); } 
      vert_id* end(void) const { return (vert_id*) (ptr+1+size()); }
      vert_id operator[](unsigned int idx) const { return ptr[1+idx]; }
      unsigned int* sparse(void) const { return sparseptr; }
      vert_id* dense(void) const { return (vert_id*) (ptr + 1); }
      unsigned int size(void) const { return *ptr; }

      bool mem(unsigned int v) const {
        unsigned int idx = sparse()[v];
        return idx < size() && dense()[idx] == v;
      }
      void add(unsigned int v) {
 //       assert(!mem(v));
//        assert(dense()+v < sparse());
        unsigned int idx = *ptr;
        dense()[idx] = v;
        sparse()[v] = idx;
        (*ptr)++;
      }
      void remove(unsigned int v) {
//        assert(mem(v));
        (*ptr)--;
        unsigned int idx = sparse()[v];
        unsigned int w = dense()[*ptr];
        dense()[idx] = w;
        sparse()[w] = idx;
      }
      void clear() { *ptr = 0; }

    protected:
      unsigned int* ptr;
      unsigned int* sparseptr;
    };

    typedef adj_list succ_range;
    typedef adj_list pred_range;

    adj_list succs(vert_id v) const
    {
      return adj_list(fwd_adjs + v*(2*max_sz+1), max_sz);
    }
    adj_list preds(vert_id v) const
    {
      return adj_list(rev_adjs + v*(2*max_sz+1), max_sz);
    }

    // growTo shouldn't be used after forget
    void growTo(unsigned int new_sz)
    {
      growCap(new_sz);
      for(; sz < new_sz; sz++)
      {
        succs(sz).clear();
        preds(sz).clear();
        is_free.push_back(false);
      }
      // GKG: Need to be careful about free_ids.
    }

  protected:
    // Allocate new memory, and duplicate 
    // the content.
    // Add an element 
    void _adj_add(unsigned int* adj, unsigned int max, unsigned int val)
    {
      adj[1 + *adj] = val;
      adj[1 + max + val] = *adj;
      (*adj)++;
    }

    void growCap(unsigned int new_max)
    {
//      check_adjs();
      if(new_max <= max_sz)
        return;

      unsigned int new_mtxsz = new_max*new_max;
      unsigned int new_adjsz = (2*new_max)+1;

      Wt* new_mtx = (Wt*) malloc(sizeof(Wt)*new_mtxsz);
      unsigned int* new_fwd = (unsigned int*) malloc(sizeof(unsigned int)*new_max*new_adjsz);
      assert(new_fwd);
      unsigned int* new_rev = (unsigned int*) malloc(sizeof(unsigned int)*new_max*new_adjsz);
      assert(new_rev);

      for(vert_id v = 0; v < sz; v++)
      {
        if(is_free[v])
          continue;
        assert(v < new_max);

        unsigned int* new_fwd_ptr = new_fwd + v*new_adjsz; 
        *new_fwd_ptr = 0;
        for(vert_id d : succs(v))
        {
          assert(d < new_max);
          _adj_add(new_fwd_ptr, new_max, d);
//          new_mtx[v*new_max + d] = mtx[v*max_sz + d];
          new (&(new_mtx[v*new_max + d])) Wt(mtx[v*max_sz+d]);
          (&(mtx[max_sz*v + d]))->~Wt();
        }

        unsigned int* new_rev_ptr = new_rev + v*new_adjsz;
        *new_rev_ptr = 0;
        for(vert_id s : preds(v))
        {
          assert(s < new_max);
          _adj_add(new_rev_ptr, new_max, s);
        }
      }
      free(mtx); 
      free(fwd_adjs);
      free(rev_adjs);

      mtx = new_mtx;
      fwd_adjs = new_fwd;
      rev_adjs = new_rev;

      max_sz = new_max;

//      check_adjs();
    }

    void write(std::ostream& o) {
      o << "[|";
      bool first = true;
      for(vert_id v = 0; v < sz; v++)
      {
        auto it = succs(v).begin();
        auto end = succs(v).end();

        if(it != end)
        {
          if(first)
            first = false;
          else
            o << ", ";

          o << "[v" << v << " -> ";
          o << "(" << edge_val(v, *it) << ":" << *it << ")";
          for(++it; it != end; ++it)
          {
            o << ", (" << edge_val(v, *it) << ":" << *it << ")";
          }
          o << "]";
        }
      }
      o << "|]";
    }

    unsigned int max_sz;
    unsigned int sz;
    float growth_rate;
    unsigned int edge_count;

    // Each element of fwd/rev adjs:
    // [ sz/1 | dense/max_sz | inv/max_sz ]
    // Total size: sizeof(uint) * max_sz * (1 + 2*max_sz)
    unsigned int* fwd_adjs;
    unsigned int* rev_adjs;
    Wt* mtx;

    std::vector<bool> is_free;
    std::vector<int> free_id;
};

}
#endif

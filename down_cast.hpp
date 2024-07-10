#pragma once

// You must include all the necessary __cxxabiv1 header
// files before including this header file

#include <cassert>      // assert
#include <concepts>     // derived_from
#include <typeinfo>     // typeid, type_info
#include <type_traits>  // is_const, is_pointer, is_polymorphic, is_volatile, remove_cvref, remove_pointer

template<typename DstPtr, typename SrcPtr>
requires (std::is_pointer_v<DstPtr> && std::is_pointer_v<SrcPtr>)
DstPtr down_cast (SrcPtr const src_ptr)
{
  using Dst = std::remove_pointer_t<DstPtr>;
  using Src = std::remove_pointer_t<SrcPtr>;

  static_assert(std::is_polymorphic_v<Dst>, "Destination type must be polymorphic.");
  static_assert(std::derived_from<Dst,Src>, "Source type must be a public base class of Destination type.");

  static_assert( std::is_const_v   <Dst> || !std::is_const_v<Src>   );
  static_assert( std::is_volatile_v<Dst> || !std::is_volatile_v<Src>);

  using namespace __cxxabiv1;

  __class_type_info const *const dst_type = dynamic_cast<__class_type_info const *>(&typeid(std::remove_cvref_t<Dst>));
  __class_type_info const *const src_type = dynamic_cast<__class_type_info const *>(&typeid(*src_ptr));
  assert( nullptr != dst_type );
  assert( nullptr != src_type );

  if (__builtin_expect(!src_ptr, 0))
    return NULL; // Handle precondition violations gracefully.

  const void *vtable = *static_cast <const void *const *>(static_cast<void*>(src_ptr));
  const vtable_prefix *prefix =
    (adjust_pointer <vtable_prefix>
     (vtable,  -ptrdiff_t (offsetof (vtable_prefix, origin))));
  const void *whole_ptr =
      adjust_pointer <void> (src_ptr, prefix->whole_object);
  const __class_type_info *whole_type = prefix->whole_type;
  __class_type_info::__dyncast_result result;

  // If the whole object vptr doesn't refer to the whole object type, we're
  // in the middle of constructing a primary base, and src is a separate
  // base.  This has undefined behavior and we can't find anything outside
  // of the base we're actually constructing, so fail now rather than
  // segfault later trying to use a vbase offset that doesn't exist.
  const void *whole_vtable = *static_cast <const void *const *> (whole_ptr);
  const vtable_prefix *whole_prefix =
    (adjust_pointer <vtable_prefix>
     (whole_vtable, -ptrdiff_t (offsetof (vtable_prefix, origin))));
  if (whole_prefix->whole_type != whole_type)
    return NULL;

  whole_type->__do_dyncast (-1, __class_type_info::__contained_public,
                            dst_type, whole_ptr, src_type, src_ptr, result);
  if (!result.dst_ptr)
    return NULL;
  if (contained_public_p (result.dst2src))
    // Src is known to be a public base of dst.
    return static_cast<DstPtr>(const_cast <void *> (result.dst_ptr));
  if (contained_public_p (__class_type_info::__sub_kind
			  (result.whole2src & result.whole2dst)))
    // Both src and dst are known to be public bases of whole. Found a valid
    // cross cast.
    return NULL;  // ---- we do not want a valid cross-cast
  if (contained_nonvirtual_p (result.whole2src))
    // Src is known to be a non-public nonvirtual base of whole, and not a
    // base of dst. Found an invalid cross cast, which cannot also be a down
    // cast
    return NULL;
  if (result.dst2src == __class_type_info::__unknown)
    result.dst2src = dst_type->__find_public_src (-1, result.dst_ptr,
                                                  src_type, src_ptr);
  if (contained_public_p (result.dst2src))
    // Found a valid down cast
    return static_cast<DstPtr>(const_cast <void *> (result.dst_ptr));
  // Must be an invalid down cast, or the cross cast wasn't bettered
  return NULL;
}

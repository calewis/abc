/**CFile****************************************************************

  FileName    [aigTable.c]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [AIG package.]

  Synopsis    [Structural hashing table.]

  Author      [Alan Mishchenko]
  
  Affiliation [UC Berkeley]

  Date        [Ver. 1.0. Started - April 28, 2007.]

  Revision    [$Id: aigTable.c,v 1.00 2007/04/28 00:00:00 alanmi Exp $]

***********************************************************************/

#include "aig.h"

ABC_NAMESPACE_IMPL_START


////////////////////////////////////////////////////////////////////////
///                        DECLARATIONS                              ///
////////////////////////////////////////////////////////////////////////

// hashing the node
static unsigned long Aig_Hash( Aig_Obj_t * pObj, int TableSize ) 
{
    unsigned long Key = Aig_ObjIsExor(pObj) * 1699;
    Key ^= Aig_ObjFanin0(pObj)->Id * 7937;
    Key ^= Aig_ObjFanin1(pObj)->Id * 2971;
    Key ^= Aig_ObjFaninC0(pObj) * 911;
    Key ^= Aig_ObjFaninC1(pObj) * 353;
    return Key % TableSize;
}

// returns the place where this node is stored (or should be stored)
static Aig_Obj_t ** Aig_TableFind( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t ** ppEntry;
    assert( Aig_ObjChild0(pObj) && Aig_ObjChild1(pObj) );
    assert( Aig_ObjFanin0(pObj)->Id < Aig_ObjFanin1(pObj)->Id );
    for ( ppEntry = p->pTable + Aig_Hash(pObj, p->nTableSize); *ppEntry; ppEntry = &(*ppEntry)->pNext )
        if ( *ppEntry == pObj )
            return ppEntry;
    assert( *ppEntry == NULL );
    return ppEntry;
}

////////////////////////////////////////////////////////////////////////
///                     FUNCTION DEFINITIONS                         ///
////////////////////////////////////////////////////////////////////////
 
/**Function*************************************************************

  Synopsis    [Resizes the table.]

  Description [Typically this procedure should not be called.]
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableResize( Aig_Man_t * p )
{
    Aig_Obj_t * pEntry, * pNext;
    Aig_Obj_t ** pTableOld, ** ppPlace;
    int nTableSizeOld, Counter, i;
    abctime clk;
    assert( p->pTable != NULL );
clk = Abc_Clock();
    // save the old table
    pTableOld = p->pTable;
    nTableSizeOld = p->nTableSize;
    // get the new table
    p->nTableSize = Abc_PrimeCudd( 2 * Aig_ManNodeNum(p) ); 
    p->pTable = ABC_ALLOC( Aig_Obj_t *, p->nTableSize );
    memset( p->pTable, 0, sizeof(Aig_Obj_t *) * p->nTableSize );
    // rehash the entries from the old table
    Counter = 0;
    for ( i = 0; i < nTableSizeOld; i++ )
    for ( pEntry = pTableOld[i], pNext = pEntry? pEntry->pNext : NULL; 
          pEntry; pEntry = pNext, pNext = pEntry? pEntry->pNext : NULL )
    {
        // get the place where this entry goes in the table 
        ppPlace = Aig_TableFind( p, pEntry );
        assert( *ppPlace == NULL ); // should not be there
        // add the entry to the list
        *ppPlace = pEntry;
        pEntry->pNext = NULL;
        Counter++;
    }
    assert( Counter == Aig_ManNodeNum(p) );
//    printf( "Increasing the structural table size from %6d to %6d. ", nTableSizeOld, p->nTableSize );
//    ABC_PRT( "Time", Abc_Clock() - clk );
    // replace the table and the parameters
    ABC_FREE( pTableOld );
}

/**Function*************************************************************

  Synopsis    [Checks if node with the given attributes is in the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_TableLookup( Aig_Man_t * p, Aig_Obj_t * pGhost )
{
    Aig_Obj_t * pEntry;
    Aig_Obj_t * pFanin0, * pFanin1;
    unsigned uType, uHash;
    assert( !Aig_IsComplement(pGhost) );
    assert( Aig_ObjIsNode(pGhost) );
    assert( Aig_ObjChild0(pGhost) && Aig_ObjChild1(pGhost) );
    assert( Aig_ObjFanin0(pGhost)->Id < Aig_ObjFanin1(pGhost)->Id );
    if ( p->pTable == NULL || !Aig_ObjRefs(Aig_ObjFanin0(pGhost)) || !Aig_ObjRefs(Aig_ObjFanin1(pGhost)) )
        return NULL;
    pFanin0 = pGhost->pFanin0;
    pFanin1 = pGhost->pFanin1;
    uType   = pGhost->Type;
    uHash   = Aig_Hash( pGhost, p->nTableSize );
    for ( pEntry = p->pTable[uHash]; pEntry; pEntry = pEntry->pNext )
    {
        if ( pEntry->pFanin0 == pFanin0 && 
             pEntry->pFanin1 == pFanin1 && 
             pEntry->Type == uType )
            return pEntry;
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Checks if node with the given attributes is in the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
Aig_Obj_t * Aig_TableLookupTwo( Aig_Man_t * p, Aig_Obj_t * pFanin0, Aig_Obj_t * pFanin1 )
{
    Aig_Obj_t * pEntry, * pR0, * pR1, * pTemp;
    unsigned uKey, uHash;

    // consider simple cases
    if ( pFanin0 == pFanin1 )
        return pFanin0;
    if ( pFanin0 == Aig_Not(pFanin1) )
        return Aig_ManConst0(p);
    pR0 = Aig_Regular(pFanin0);
    pR1 = Aig_Regular(pFanin1);
    if ( pR0 == p->pConst1 )
        return pFanin0 == p->pConst1 ? pFanin1 : Aig_ManConst0(p);
    if ( pR1 == p->pConst1 )
        return pFanin1 == p->pConst1 ? pFanin0 : Aig_ManConst0(p);
    if ( p->pTable == NULL )
        return NULL;
    if ( pR0->nRefs == 0 || pR1->nRefs == 0 )
        return NULL;

    // canonicalize order (smaller ID first)
    if ( pR0->Id > pR1->Id )
    {
        pTemp = pFanin0; pFanin0 = pFanin1; pFanin1 = pTemp;
        pTemp = pR0; pR0 = pR1; pR1 = pTemp;
    }

    // compute hash key directly
    uKey  = (unsigned)pR0->Id * 7937;
    uKey ^= (unsigned)pR1->Id * 2971;
    uKey ^= (unsigned)Aig_IsComplement(pFanin0) * 911;
    uKey ^= (unsigned)Aig_IsComplement(pFanin1) * 353;
    uHash = uKey % (unsigned)p->nTableSize;

    // search bucket: compare fanin pointers directly
    for ( pEntry = p->pTable[uHash]; pEntry; pEntry = pEntry->pNext )
    {
        if ( pEntry->pFanin0 == pFanin0 && pEntry->pFanin1 == pFanin1 && pEntry->Type == AIG_OBJ_AND )
            return pEntry;
    }
    return NULL;
}

/**Function*************************************************************

  Synopsis    [Adds the new node to the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableInsert( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    unsigned uHash;
    assert( !Aig_IsComplement(pObj) );
    assert( Aig_TableLookup(p, pObj) == NULL );
    if ( (pObj->Id & 0xFF) == 0 && 2 * p->nTableSize < Aig_ManNodeNum(p) )
        Aig_TableResize( p );
    uHash = Aig_Hash( pObj, p->nTableSize );
    pObj->pNext = p->pTable[uHash];
    p->pTable[uHash] = pObj;
}

/**Function*************************************************************

  Synopsis    [Deletes the node from the hash table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
void Aig_TableDelete( Aig_Man_t * p, Aig_Obj_t * pObj )
{
    Aig_Obj_t ** ppPlace;
    assert( !Aig_IsComplement(pObj) );
    ppPlace = Aig_TableFind( p, pObj );
    assert( *ppPlace == pObj ); // node should be in the table
    // remove the node
    *ppPlace = pObj->pNext;
    pObj->pNext = NULL;
}

/**Function*************************************************************

  Synopsis    [Count the number of nodes in the table.]

  Description []
               
  SideEffects []

  SeeAlso     []

***********************************************************************/
int Aig_TableCountEntries( Aig_Man_t * p )
{
    Aig_Obj_t * pEntry;
    int i, Counter = 0;
    for ( i = 0; i < p->nTableSize; i++ )
        for ( pEntry = p->pTable[i]; pEntry; pEntry = pEntry->pNext )
            Counter++;
    return Counter;
}

/**Function********************************************************************

  Synopsis    [Profiles the hash table.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Aig_TableProfile( Aig_Man_t * p )
{
    Aig_Obj_t * pEntry;
    int i, Counter;
    printf( "Table size = %d. Entries = %d.\n", p->nTableSize, Aig_ManNodeNum(p) );
    for ( i = 0; i < p->nTableSize; i++ )
    {
        Counter = 0;
        for ( pEntry = p->pTable[i]; pEntry; pEntry = pEntry->pNext )
            Counter++;
        if ( Counter ) 
            printf( "%d ", Counter );
    }
}

/**Function********************************************************************

  Synopsis    [Profiles the hash table.]

  Description []

  SideEffects []

  SeeAlso     []

******************************************************************************/
void Aig_TableClear( Aig_Man_t * p )
{
    ABC_FREE( p->pTable );
    p->nTableSize = 0;
}

////////////////////////////////////////////////////////////////////////
///                       END OF FILE                                ///
////////////////////////////////////////////////////////////////////////


ABC_NAMESPACE_IMPL_END


﻿module SmartPortOrder
open Elmish
open Fable.React.Props
open CommonTypes
open Fable.React
open DrawModelType
open DrawModelType.SymbolT
open DrawModelType.BusWireT
open Symbol
open Optics
open Operators
open SmartHelpers


//HLP23: Indraneel


/// Created my own function that returns an option
/// in the form of an updated List otherwise None
let tryUpdateAt index value list =
    if index >= 0 && index < List.length list then
        Some (List.updateAt index value list)
    else
        None

  
/// Takes as input the portList and creates a portList' that contains
/// the indexes of all the ports.
/// Selects either the max/min based on the edge
let findMinIndex (symbol: Symbol) (portList) (edge: Edge) =

    let portList' = 
        portList
        |> List.collect (fun id -> 
            match symbol.PortMaps.Order[edge] |> List.tryFindIndex (fun elm -> elm = id) with
            | Some index -> [index]
            | None -> [])

    match edge with
    | Top | Right -> 
        List.min portList'
    | Bottom | Left -> 
        List.max portList'

/// Takes as input the portList and creates a portList' that contains
/// the indexes of all the ports.
/// Selects either the max/min based on the edge
let findMaxIndex (symbol: Symbol) (portList) (edge: Edge) =

    let portList' = 
        portList
        |> List.collect (fun id -> 
            match symbol.PortMaps.Order[edge] |> List.tryFindIndex (fun elm -> elm = id) with
            | Some index -> [index]
            | None -> [])

    match edge with
    | Top | Right -> 
        List.max portList'
    | Bottom | Left ->
        List.min portList'

/// Find the translated index in the case when a wire doesn't start at index 0
/// or all the ports don't have a wire connected to them
let findTranslatedIndex (interWires: list<Wire>) (symbolToOrder: Symbol) 
    (otherSymbol: Symbol) (inputEdge: Edge) (outputEdge: Edge)
    (newInputList: list<string>) (newOutputList: list<string>) = 

    let outputPortList = 
        interWires
            |> List.map(fun wire -> string wire.OutputPort)

    let inputPortList = 
        interWires
        |> List.map(fun wire -> string wire.InputPort)

    let outputLength = newOutputList.Length - 1
    let inputLength = newInputList.Length - 1

    if (inputLength = outputLength) then
        0
    else
        match inputEdge, outputEdge with
        | Top, Bottom | Bottom, Top | Left, Right | Right, Left | Left, Top | Bottom, Right ->
            if inputLength > outputLength then
                let inputMinIndex = findMinIndex symbolToOrder inputPortList inputEdge
                printfn "Diff input > output: %A" -(inputLength - inputMinIndex)
                -(inputLength - inputMinIndex)
            else
                let outputMinIndex = findMinIndex otherSymbol outputPortList outputEdge
                printfn "Diff else: %A" outputMinIndex
                outputMinIndex
        
        | Top, Top | Top, Left | Right, Bottom ->
            if inputLength > outputLength then
                let inputMaxIndex = findMaxIndex symbolToOrder inputPortList inputEdge
                printfn "Diff input > output: %A" -(inputLength - inputMaxIndex)
                -(inputLength - inputMaxIndex)
            else
                let outputMaxIndex = findMaxIndex otherSymbol outputPortList outputEdge
                printfn "Diff else: %A" outputMaxIndex
                outputMaxIndex

        | Bottom, Bottom | Left, Left | Bottom, Left | Left, Bottom ->
                if inputLength > outputLength then
                    let inputMinIndex = findMinIndex symbolToOrder inputPortList inputEdge
                    printfn "Diff input>output: %A" -(inputLength - inputMinIndex)
                    -(inputLength - inputMinIndex)
                else
                    let outputMaxIndex = findMaxIndex otherSymbol outputPortList outputEdge
                    printfn "Diff else: %A" outputMaxIndex
                    outputMaxIndex

        | Right, Right | Top, Right | Right, Top ->
            if inputLength > outputLength then
                let inputMaxIndex = findMaxIndex symbolToOrder inputPortList inputEdge
                printfn "Diff input>output: %A" -(inputLength - inputMaxIndex)
                -(inputLength - inputMaxIndex)
            else
                let outputMinIndex = findMinIndex otherSymbol outputPortList outputEdge
                printfn "Diff else: %A" outputMinIndex
                outputMinIndex

/// Gets new input and output port maps that only
/// contain ports that have wires connected to them
/// between the 2 symbols
let getNewPortMap (symbolToOrder: Symbol) (otherSymbol: Symbol)
    (inputEdge: Edge) (outputEdge: Edge) 
    (interWires: list<Wire>) = 

    let outputPortList = 
        interWires
        |> List.map(fun wire -> string wire.OutputPort)

    let inputPortList = 
        interWires
        |> List.map(fun wire -> string wire.InputPort)

    let filteredInputEdge = 
        symbolToOrder.PortMaps.Order[inputEdge] 
        |> List.filter (fun x -> List.contains x inputPortList)

    let filteredOutputEdge = 
        otherSymbol.PortMaps.Order[outputEdge]
        |> List.filter (fun x -> List.contains x outputPortList)

    filteredInputEdge, filteredOutputEdge


/// Changes old PortMaps by taking a slice of them and updating
/// then adding the slice back into the old position
/// returns the portMap List containing an updated order
let changeOldPortMaps (symbolToOrder: Symbol) (newPortMapList: list<string>) (edge: Edge) 
    (indexChange:int) (inputPortId: string) = 

    let newLength = newPortMapList.Length

    let minIndex = 
            newPortMapList
            |> List.collect (fun id -> 
                match symbolToOrder.PortMaps.Order[edge] |> List.tryFindIndex (fun elm -> elm = id) with
                | Some index -> [index]
                | None -> [])
            |> List.min
    
 
    let returnSliceList (start:int) (length:int) list =
        list
        |> Seq.skip start
        |> Seq.take length
        |> List.ofSeq

    let slicedList = returnSliceList minIndex newLength symbolToOrder.PortMaps.Order[edge]

    let newOrderWithRemovedElements = 
        symbolToOrder.PortMaps.Order[edge] 
        |> List.removeManyAt minIndex newLength

    let newSlicedList = 
        match (tryUpdateAt indexChange inputPortId slicedList)  with
        | Some newList -> newList
        | None -> 
            printfn "Index out of range"
            slicedList

    printfn " oldSHortList: %A \n newShortList: %A" slicedList newSlicedList
    
    let front, back = 
        newOrderWithRemovedElements 
        |> List.splitAt minIndex


    front @ newSlicedList @ back
  


/// Base Function which changes reOrders the ports in symbolToOrder
/// It picks up the selection of wires and provides new indexes
/// to re-orient itself and puts the new list back into the array
let changePortOrder (wModel: BusWireT.Model)
    (symbolToOrder: Symbol) 
    (otherSymbol: Symbol)
    (interWires: list<Wire>) =

    let sModel = wModel.Symbol

    printfn $"ReorderPorts: ToOrder:{symbolToOrder.Component.Label} {symbolToOrder.Id }, Other:{otherSymbol.Component.Label}"
 
    let updatedSymbol = 
        (symbolToOrder, interWires)
        ||> List.fold (fun symbol wire -> 

            let outputPortId = wire.OutputPort // port id of wire exiting
            let inputPortId = wire.InputPort // port id of  wire entering
                        
            let outputEdge = getPortOrientation sModel  (OutputId outputPortId)
            let inputEdge = getPortOrientation sModel  (InputId inputPortId)
           
            /// returns an updated symbol with New port Maps
            let newPortMapOrder =

                let newInputList, newOutputList = getNewPortMap symbol otherSymbol inputEdge outputEdge interWires

                let outputPortIndex =
                    match newOutputList |> List.tryFindIndex (fun elm -> elm = string outputPortId) with 
                    | Some index -> index
                    | None -> 
                        printfn "Couldn't find index in outputPortIndex "
                        0

                let remainder = findTranslatedIndex interWires symbol otherSymbol inputEdge outputEdge newInputList newOutputList
                let indexChange = newInputList.Length - (outputPortIndex) - 1 + remainder
                let newPortMapList' = changeOldPortMaps symbol newInputList inputEdge indexChange (string inputPortId)

                printfn " Port Index: %A  %A" outputPortIndex indexChange
                printfn "PortMapList' is: %A" newPortMapList'
              
                let newOrder = 
                    symbol.PortMaps.Order
                        |> Map.add inputEdge newPortMapList'

                newOrder
            
            { symbol with PortMaps = { symbol.PortMaps with Order = newPortMapOrder} }
            )

    updatedSymbol


/// Finds all the InterConnecting Wires between 2 symbols given WireModel.Wires and the 2 symbols
/// and a flag to get either all interconnecting wires or just wires in the direction from otherSymbol->symbolToOrder
let findInterconnectingWires (wireList:List<Wire>) (sModel)
    (symbolToOrder:Symbol) 
    (otherSymbol:Symbol) (getAllConnections:int) =
        
    wireList
    |> List.filter (fun value ->

        let inputPortHostId = string sModel.Ports[string value.InputPort].HostId
        let outputPortHostId = string  sModel.Ports[string value.OutputPort].HostId

        let symbolToOrderId = string symbolToOrder.Id
        let otherSymbolId = string otherSymbol.Id
        
        if (getAllConnections = 0) then
            (inputPortHostId = symbolToOrderId) && (outputPortHostId = otherSymbolId)
        else
            if ((inputPortHostId = symbolToOrderId) && (outputPortHostId = otherSymbolId)) then true
            elif ((inputPortHostId = otherSymbolId) && (outputPortHostId = symbolToOrderId)) then true
            else false

        )



let compareMaps (newMap: Map<_, _>) (oldMap: Map<_, _>) : Map<_, _> =

    let newMapList = Map.toList newMap |> List.map snd
    let oldMapList = Map.toList oldMap |> List.map snd

    if List.length newMapList = List.length oldMapList then
        let areEqual =
            Seq.forall2 (fun newList oldList -> (List.distinct newList).Length = (List.distinct oldList).Length) newMapList oldMapList

        if areEqual then 
            newMap 
        else 
            printfn "Error Succesfully handled"
            oldMap
    else
        printfn "Error Succesfully handled"
        oldMap

                
/// Main Function that is called from issie
let reOrderPorts 
    (wModel: BusWireT.Model) 
    (symbolToOrder: Symbol) 
    (otherSymbol: Symbol) 
    (busWireHelper: BusWireHelpers)
        : BusWireT.Model =

    printfn $"ReorderPorts: ToOrder:{symbolToOrder.Component.Label}, Other:{otherSymbol.Component.Label}"

    let sModel = wModel.Symbol
    let OriginalPortMap = symbolToOrder.PortMaps.Order

    let wireList =
        wModel.Wires
        |> Map.toList
        |> List.map snd

    let allWires = findInterconnectingWires wireList sModel symbolToOrder otherSymbol 1
    let wiresToOrder = findInterconnectingWires allWires sModel symbolToOrder otherSymbol 0 

    printfn "Wire length is %A" wiresToOrder.Length

    match wiresToOrder.Length with 
    | n when n > 1 ->
     
        let symbol' = changePortOrder wModel symbolToOrder otherSymbol wiresToOrder
        let symbolPortMap' = symbol'.PortMaps.Order
        
        let PortMap = compareMaps symbolPortMap' OriginalPortMap
        let symbol'' = { symbol' with PortMaps = { symbol'.PortMaps with Order = PortMap} }

        let newModel = 
            {wModel with 
                Symbol = {sModel with Symbols = Map.add symbol'.Id symbol'' sModel.Symbols}
            }

        let wModel' = busWireHelper.updateSymbolWires newModel symbol'.Id
     
        wModel'
    | _ ->
        printfn " No Wires between SymToOrder and otherSym"
        wModel





/// HLP23: Indraneel
/// Applies port reordering across entire sheet
let singleReOrder 
    (wModel: BusWireT.Model) 
    (symbolToOrder: Symbol)
    (busWireHelper: BusWireHelpers)
        : BusWireT.Model =

    printfn $"Ordering the Single Component {symbolToOrder.Component.Label}"
    let sModel = wModel.Symbol

    let wireList =
        wModel.Wires
        |> Map.toList
        |> List.map snd


    let inputSymbols = 
        wireList 
        |> List.collect(fun value ->

        let outputPortHostId = ComponentId  sModel.Ports[string value.OutputPort].HostId
        [sModel.Symbols[outputPortHostId]]
        )

        |> List.distinct

    let wModel' = 
        (wModel, inputSymbols)
        ||> List.fold (fun model otherSymbol ->   
            reOrderPorts model symbolToOrder otherSymbol busWireHelper
        )

    wModel'


/// HLP23: AUTHOR Indraneel & Ifte
/// Applies port reordering across entire sheet
let sheetReOrderPorts 
    (wModel: BusWireT.Model) 
    (busWireHelper: SmartHelpers.BusWireHelpers)
        : BusWireT.Model =

    printfn $"Ordering the whole sheet"

    let wIdList =
        wModel.Wires
        |> Map.toList
        |> List.map fst

    let wModel' = 
        (wModel, wIdList)
        ||> List.fold (fun model wId ->

            let sModel = model.Symbol
            let currWire = model.Wires[wId]

            let wireList =
                model.Wires
                |> Map.toList
                |> List.map snd

            let outputPortId = string currWire.OutputPort
            let inputPortId = string currWire.InputPort

            let symbolToOrder = getSymbol sModel inputPortId
            let otherSymbol = getSymbol sModel outputPortId

            let connWireList = findInterconnectingWires wireList sModel symbolToOrder otherSymbol 0

            let symbol = changePortOrder model symbolToOrder otherSymbol connWireList

            let sModel' = {sModel with Symbols = Map.add symbol.Id symbol sModel.Symbols}
            let model' = {model with Symbol = sModel'}

            busWireHelper.updateSymbolWires model' symbol.Id
        )

    wModel'
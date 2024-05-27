<style>
#proof-canvas {
    width: 100%;
    height: 100%;
    background-color: white;
    overflow: hidden;
}

#menuIcons {
    display: none;
}

.selectable {
    /* border-color: rgba(255, 153, 51, 0.3);
    background-color: rgba(255, 153, 51, 0.3);
    color: black; */
    color: purple;
    background-color: plum;
}

.selected {
    /* border-color: rgb(255, 153, 51)!important;
    background-color: rgb(255, 153, 51)!important; */
    color: purple;
    background-color: plum;
}

/*
 * style apply to all span that have an id containing ":"
 * Add transparent border left and right, so size of the div won't change
 * when highlight (with border) appears
 */
.pi-btn span[id*=":"] {
    border-left: 1px solid transparent;
    border-right: 1px solid transparent;
}

/* sub-targets style during a DND */
.pi-btn span[id*=":"].highlight {
    /* color: OrangeRed; */
    border: 1px solid black;
}

/* sub-targets style during a DND when source is over destination */
.pi-btn span[id*=":"].dropover {
    /* border-color: OrangeRed;
    background-color: OrangeRed;
    color: black; */

    color: blue;
    border: 1px solid blue;
}

.pi-btn span[id*=":"].dropdestination {
    color: white;
    background-color: #888;
}

/* sub-target style when source is over sub-target */
.pi-btn span[id*=":"].droptarget {
    color: white;
    background: red;
    border: 2px solid red;
}

/* Invert colors for a goal beeing dragged */
.pi-btn.pi-goal.dragged span[id*=":"].droptarget {
    color: red;
    background: white;
    border: 2px solid white;
}

.pi-btn.dragged {
    overflow: hidden;
    border: none;
}

.prover-msg {
    position: fixed;
    bottom: 20px;
    left: 0;
    right: 0;
    min-width: 400px;
    max-width: 800px;
    margin: 0px-auto;
    text-align: center;
    opacity: 0;
    transition: opacity 0s ease-in;
}

.prover-msg.shown {
    opacity: 1;
    transition: opacity 0.3s ease-in;
}

.canvas {
    position: relative;
}


.work-zone {
    padding-left: 15px;
    padding-right: 15px;
}

.hypothesis-zone {
    padding-left: 15px;
    padding-right: 15px;
}

.lemmas-zone {
    padding-left: 15px;
    padding-right: 5px;
}

.nav-tabs {
    background-color: #eee;
}

.tab-content {
    height: calc(100% - 47px);
    position: relative;
}

#subgoal-content .tab-pane {
    height: 100%;
    position: relative;
}

.dragbar {
    height: 100%;
    width: 5px;
    background-color: #e7e7e7;
    display: inline-block;
    cursor: col-resize;
}


.pi-btn:focus,
.pi-btn:active {
    outline: none !important;
}

:focus,
.btn:focus {
    outline: none !important;
}
</style>

<template>
    <div id="proof-canvas" class="container-fluid" @click="unhighlight" @contextmenu="openActionsMenu">
        <div id="menuIcons"></div>
        <div class="row" style="height: 100%;">
            <div class="col" style="padding: 0;" :key="renderIndex">
                <template v-if="proofState">
                    <template v-if="this.qed">
                        <fireworks></fireworks>
                    </template>

                    <template v-else>
                        <ul class="nav nav-tabs" id="subgoal-tab" role="tablist">
                            <li class="nav-item" v-for="(subgoal, i) in proofState.subgoals()" :key="subgoal.handle">
                                <a class="nav-link text-danger" :class="{ active: isActiveSubgoal(i) }"
                                    :id="getSubgoalId(subgoal) + '-tab'" data-toggle="tab"
                                    :href="'#' + getSubgoalId(subgoal)" role="tab"
                                    :aria-controls="getSubgoalId(subgoal)" aria-selected="true" :data-subgoal="i"
                                    v-html="getSubgoalString(subgoal)" @click="setTab(i)"></a>
                            </li>
                        </ul>
                        <div class="tab-content" id="subgoal-content">
                            <div v-for="(subgoal, i) in proofState.subgoals()" :key="subgoal.handle"
                                class="tab-pane fade" :class="{ show: isActiveSubgoal(i), active: isActiveSubgoal(i) }"
                                :id="getSubgoalId(subgoal)" :aria-labelledby="getSubgoalId(subgoal) + '-tab'">
                                <div class="canvas row" style="height: 100%; position: relative;">
                                    <div class="lemmas-zone" :style="{ width: (hypsZoneStart * docWidth) + 'px' }">
                                        <lemma-search :goal="subgoal" :context="subgoal.context()"
                                            :vars="subgoal.vars()" :selectMode="selectMode" :displayMode="displayMode"
                                            ref="lsearch"></lemma-search>
                                    </div>
                                    <div class=" dragbar" ref="dragbar-left" @mousedown="startDragLeft"></div>
                                    <div class="hypothesis-zone" @click="deselect"
                                        :style="{ width: ((hypsZoneEnd - hypsZoneStart) * docWidth) + 'px' }">
                                        <proposition-list :goal="subgoal" :context="subgoal.context()"
                                            :vars="subgoal.vars()" :selectMode="selectMode" :displayMode="displayMode"
                                            ref="plist"></proposition-list>
                                    </div>
                                    <div class="dragbar" ref="dragbar-right" @mousedown="startDragRight"></div>
                                    <div class="work-zone" droppable="true" @drop="onDropPredicate"
                                        @dragover="onDragOverPredicate" @click="deselect">
                                        <goal :subgoal="subgoal" :key="getGoalKey(i)" :selectMode="selectMode"
                                            :displayMode="displayMode" :ref="subgoal.handle"></goal>
                                        <predicate v-for="(predicate, j) in getPredicatesInWorkZone(subgoal)"
                                            :predicate="predicate" :selectMode="selectMode" :displayMode="displayMode"
                                            :key="getPredicateKey(i, j)" :ref="predicate.handle"></predicate>
                                        <expression v-for="expression in getExpressionsInWorkZone(subgoal)"
                                            :expression="expression" :selectMode="selectMode" :displayMode="displayMode"
                                            :key="expression.handle" draggable="true" :ref="expression.handle">
                                        </expression>
                                    </div>
                                </div>
                            </div>
                            <RadialMenu ref="actionsMenu"
                                :style="{ 'z-index': 10, top: actionsMenu.y + 'px', left: actionsMenu.x + 'px' }"
                                @clicked="actionsMenuClicked" @closed="actionsMenuClosed"
                                :menu-items="actionsMenu.items" :size="actionsMenu.size" close-on-click></RadialMenu>
                        </div>
                    </template>
                </template>
                <div class="alert alert-danger mx-auto prover-msg" :class="{ shown: errorMsg !== null }" role="alert">
                    {{ errorMsg }}
                </div>
                <div class="alert alert-warning mx-auto prover-msg" :class="{ shown: warningMsg !== null }"
                    role="alert">
                    {{ warningMsg }}
                </div>
            </div>
        </div>
    </div>
</template>

<script>
import _ from "lodash";

import PropositionListVue from "./propositionList.vue";
import LemmaSearchVue from "./lemmaSearch.vue";
import ExpressionVue from "./expression.vue";
import PredicateVue from "./predicate.vue";
import GoalVue from "./goal.vue";
import FireWorksVue from "./fireworks.vue";
import RadialMenu from "./RadialMenu/RadialMenu.vue"

export default {
    components: {
        "proposition-list": PropositionListVue,
        "lemma-search": LemmaSearchVue,
        predicate: PredicateVue,
        expression: ExpressionVue,
        goal: GoalVue,
        fireworks: FireWorksVue,
        RadialMenu
    },
    data: function () {
        return {
            qed: false,
            proofState: null,
            errorMsg: null,
            warningMsg: null,

            hypsZoneStart_: 0.30,
            hypsZoneEnd_: 0.70,
            docWidth: null,

            renderIndex: 0,

            selectMode: false, // true if we are selecting a subpath, false otherwise
            displayMode: "html", // "html" or "mathml"

            selection: {},

            actionsMenu: {
                size: 400, x: 0, y: 0,
                items: []
            },
            menuIcons: []
        };
    },
    computed: {
        // The start of the hypotheses zone, as a percentage (between 0.0 and 1.0).
        hypsZoneStart: {
            get: function () {
                return this.hypsZoneStart_;
            },
            set: function (newStart) {
                //let hypsWidths = $(".pi-btn.in-hypothesis-zone")
                //    .map(function () { return $(this).outerWidth(); })
                //    .toArray();
                //let maxHypWidth = _.max(hypsWidths) + 80;
                //if (hypsWidths.length === 0 || newWidth >= maxHypWidth) {
                if (0.05 <= newStart && newStart <= this.hypsZoneEnd - 0.05) {
                    this.hypsZoneStart_ = newStart;
                }
                //}
            }
        },
        // The start of the hypotheses zone, as a percentage (between 0.0 and 1.0).
        hypsZoneEnd: {
            get: function () {
                return this.hypsZoneEnd_;
            },
            set: function (newEnd) {
                //let hypsWidths = $(".pi-btn.in-hypothesis-zone")
                //    .map(function () { return $(this).outerWidth(); })
                //    .toArray();
                //let maxHypWidth = _.max(hypsWidths) + 80;
                //if (hypsWidths.length === 0 || newWidth >= maxHypWidth) {
                if (this.hypsZoneStart + 0.05 <= newEnd && newEnd <= 0.95) {
                    this.hypsZoneEnd_ = newEnd;
                }
                //}
            }
        },
    },
    created: function () {
        // just a string -> action dictionnary. Actions are defined by the miniprover and are transparent,
        // but we need to retrieve them when at user-interaction time
        this.actionCodes = {};

        // store and retrieve the previous states
        this.history = [];
        this.historyIndex = -1; // ptr to the current state actually displayed

        // map path <-> vue button object
        this.pathButtonMap = {};
    },
    beforeUpdate() {
        this.actionCodes = {}; // remove all defined actions
        this.pathButtonMap = {}; // clean id <-> button map
    },
    updated: function () {
        if (this.displayMode == "mathml") {
            if (this.proofState !== null && this.proofState !== undefined) {
                // MathJax.Hub.Queue(["Typeset",MathJax.Hub]);
            }
        }
    },

    mounted: function () {
        // Set a resize watcher to compute this.docWidth.
        this.handleResize();
        window.addEventListener("resize", this.handleResize);
    },

    beforeDestroy: function () {
        window.removeEventListener("resize", this.handleResize);
    },

    methods: {
        // The user STARTS dragging the dragbar that's between the lemmas and hypotheses.
        startDragLeft: function (e) {
            e.preventDefault();
            document.addEventListener('mouseup', this.endDrag);
            document.addEventListener('mousemove', this.updateLeftDragbar);
        },

        // The user STARTS dragging the dragbar that's between the hypotheses and work-zone.
        startDragRight: function (e) {
            e.preventDefault();
            document.addEventListener('mouseup', this.endDrag);
            document.addEventListener('mousemove', this.updateRightDragbar);
        },

        // The user IS dragging the dragbar that's between the lemmas and hypotheses.
        updateLeftDragbar: function (e) {
            _.debounce(() => {
                this.hypsZoneStart = e.pageX / this.docWidth;
            }, 100)();
        },

        // The user IS dragging the dragbar that's between the hypotheses and work-zone.
        updateRightDragbar: function (e) {
            _.debounce(() => {
                this.hypsZoneEnd = e.pageX / this.docWidth;
            }, 100)();
        },

        // The user FINISHED dragging one of the two dragbars.
        endDrag: function (e) {
            e.preventDefault();
            document.removeEventListener('mouseup', this.endDrag);
            document.removeEventListener('mousemove', this.updateLeftDragbar);
            document.removeEventListener('mousemove', this.updateRightDragbar);
        },

        getGoalKey(index) {
            return "proof-" + this.proofState.handle + "-goal-" + "-" + index;
        },

        getPredicateKey(i, j) {
            return this.getGoalKey(i) + "-predicate-" + j;
        },

        // save a miniprover action code for later
        saveActionCode(id, action, code) {
            this.actionCodes[id + "|" + action] = code;
        },

        // retrieve a miniprover action code
        getActionCode(id, action) {
            return this.actionCodes[id + "|" + action];
        },

        highlight(ids) {
            _.each(ids, id => {
                $(document.getElementById(id)).addClass("highlight");
                $(document.getElementById(id))
                    .closest(".pi-btn")
                    .addClass("displaying-highlight");
            });
        },

        unhighlight() {
            $(this.$el)
                .find(".highlight")
                .removeClass("highlight")
                .removeClass("dropover")
                .removeClass("droptarget")
                .removeClass("dropdestination")
                .closest(".pi-btn")
                .removeClass("displaying-highlight");
        },

        // highlight droppable zone
        highlightDrop(divId) {
            $(document.getElementById(divId)).addClass("dropover");
        },

        unhighlightDrop() {
            $(this.$el)
                .find(".dropover")
                .removeClass("dropover")
                .removeClass("droptarget")
                .removeClass("dropdestination");
            this.unhighlightGeneralize();
        },

        // show use that we're going to drop here if mouse is released
        highlightDropTarget(divId) {
            $(document.getElementById(divId)).addClass("droptarget");
        },

        unhighlightDropTarget() {
            $(this.$el)
                .find(".droptarget")
                .removeClass("droptarget");
        },

        highlightDropDestination(divId) {
            $(document.getElementById(divId)).addClass("dropdestination");
        },

        unhighlightDropDestination() {
            $(this.$el)
                .find(".dropdestination")
                .removeClass("dropdestination");
        },

        showGeneralize() {
            $(".pi-goal .generalize").show();
        },

        hideGeneralize() {
            $(".pi-goal .generalize").hide();
        },

        highlightGeneralize() {
            let generalizeDiv = $(".pi-goal .generalize");
            generalizeDiv.addClass("highlight");
        },

        unhighlightGeneralize() {
            let generalizeDiv = $(".pi-goal .generalize");
            generalizeDiv.removeClass("highlight");
        },

        undo() {
            if (this.historyIndex > 0) {
                this.historyIndex--;
                window.goal = this.proofState = this.history[this.historyIndex];
                this.$forceUpdate();
                this.resetSelection();
            }
        },

        sendUndo() {
            try {
                window.ipcRenderer.send('undo');
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        redo() {
            if (this.historyIndex < this.history.length - 1) {
                this.historyIndex++;
                window.goal = this.proofState = this.history[this.historyIndex];
                this.$forceUpdate();
                this.resetSelection();
            }
        },

        sendRedo() {
            try {
                window.ipcRenderer.send('redo');
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        // change the proof state by applying a prover rule
        apply(actionCode) {
            try {
                var proof = this.proofState.apply(actionCode);
                this.setProofState(proof);
                this.resetSelection();
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        sendAction(actionb) {
            try {
                let idx = this.getActiveSubgoal();
                let action = { subgoalIndex: idx, repr: actionb };
                window.ipcRenderer.send('action', action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        sendActionCode(actionCode) {
            try {
                let action = window.goal.encodeaction(actionCode);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        // Send a [cut] action to the plugin.
        sendCutHypothesis(subgoal, text) {
            try {
                let action = subgoal.getcutb(text);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        // Send a [lemma] action to the plugin.
        sendLemma(subgoal, handle) {
            try {
                let action = subgoal.addlemmab(handle);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        applyNewExpression(subgoal, text) {
            try {
                var proof = subgoal.addalias(text);
                this.resetSelection();
                this.setProofState(proof);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        sendNewExpression(subgoal, text) {
            try {
                let action = subgoal.getaliasb(text);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        duplicateHyp(subgoal, hypHandle) {
            try {
                let action = subgoal.encodeduplicate(hypHandle);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },


        clearHyp(subgoal, hypHandle) {
            try {
                let action = subgoal.encodeclear(hypHandle);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        generalize(subgoal, hypHandle) {
            try {
                let action = subgoal.encodegeneralize(hypHandle);
                this.sendAction(action);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        moveHyp(subgoal, fromHandle, toHandle) {
            try {
                var proof = subgoal.movehyp(fromHandle, toHandle);
                this.setProofState(proof);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        setProofState(proofState) {
            if (!proofState) {
                this.proofState = null;
            } else {
                try {
                    console.log("Setting proof state");
                    console.log(proofState);
                    // set the current active tab since the prover doesn't transmit root metadata on apply()
                    //proofState.setmeta({ activeSubgoal: this.getActiveSubgoal() });
                    window.goal = this.proofState = proofState;
                    this.addToHistory(this.proofState);
                    this.resetSelection();
                    this.$forceUpdate();
                    this.qed = false;
                } catch (e) {
                    this.showErrorMessage("Failed to apply new proof state");
                }
            }
        },

        getProofState() {
            return this.proofState;
        },

        showErrorMessage(e) {
            console.error(e);

            var msg = "";
            if (e instanceof Error) {
                msg = (e[1] && e[1].c) || e.msg || e.toString();
            } else if (typeof e === "string") {
                msg = e;
            } else if (typeof e.toString === "function") {
                msg = e.toString();
            } else {
                msg = "" + e;
            }

            // display it for 5 sec
            this.errorMsg = msg;
            setTimeout(() => {
                this.errorMsg = null;
            }, 5000);
        },

        showWarningMessage(msg) {
            // display it for 2 sec
            this.warningMsg = msg;
            setTimeout(() => {
                this.warningMsg = null;
            }, 2000);
        },

        addToHistory(proofState) {
            this.historyIndex++;
            this.history[this.historyIndex] = proofState;

            if (this.history.length > this.historyIndex + 1) {
                // there is still history left after this new state.
                // We likely did several undo, then saved a new state.
                // We should delete the rest of the history at this point
                this.history.length = this.historyIndex + 1; // delete all the non-relevant states left
            }
        },

        getSubgoalHTML(subgoal) {
            return subgoal.conclusion().html();
        },

        getSubgoalString(subgoal) {
            return subgoal.conclusion().tostring();
        },

        getSubgoalId(subgoal) {
            return "subgoal-" + subgoal.handle;
        },

        setActiveSubgoal(index) {
            this.proofState.setmeta({ activeSubgoal: index });
        },

        setTab(index) {
            this.setActiveSubgoal(index);
        },

        getActiveSubgoal() {
            if (!this.proofState) return 0;

            var metadata = this.proofState.getmeta();
            var activeSubgoal = metadata && metadata.activeSubgoal;
            // check if the active subgoal is still valid (after ctrl-z/ctrl-y for instance)
            if (
                activeSubgoal &&
                activeSubgoal < this.proofState.subgoals().length
            ) {
                return activeSubgoal;
            } else {
                return 0;
            }
        },

        isActiveSubgoal(index) {
            return index == this.getActiveSubgoal(); // we just need to worry about init here. The rest is handled by bootstrap
        },

        debugHistory() {
            _.each(this.history, (state, i) => {
                console.log(
                    "state " + i + " : " + JSON.stringify(state.getmeta())
                );
            });
        },

        handleResize() {
            this.docWidth = document.documentElement.clientWidth;
        },

        getSelection(subgoal) {
            return this.selection[subgoal.handle] || [];
        },

        getActiveSelection() {
            let subgoal = this.proofState.subgoals()[this.getActiveSubgoal()];
            return this.getSelection(subgoal);
        },

        addSelectedPath(handle, path) {
            if (!this.selection[handle])
                this.selection[handle] = [];
            this.selection[handle].push(path);
        },

        removeSelectedPaths(handle, paths) {
            if (this.selection[handle])
                _.pull(this.selection[handle], paths);
        },

        getPredicatesInWorkZone(subgoal) {
            return _.filter(subgoal.context(), o => {
                var meta = o.getmeta();
                if (meta) {
                    return meta.inWorkZone || false;
                }
                return false;
            });
        },

        getExpressionsInWorkZone(subgoal) {
            return _.filter(subgoal.vars(), o => {
                var meta = o.getmeta();
                if (meta) {
                    return meta.inWorkZone || false;
                }
                return false;
            });
        },

        getPredicateFromHandle(handle) {
            var p = null;
            _.each(this.proofState.subgoals(), goal => {
                _.each(goal.context(), predicate => {
                    if (predicate.handle === handle) {
                        p = predicate;
                    }
                });
            });

            return p;
        },

        onDropPredicate(e) {
            var handle = e.dataTransfer.getData("handle");
            var deltaX = parseInt(e.dataTransfer.getData("deltaX"));
            var deltaY = parseInt(e.dataTransfer.getData("deltaY"));

            var predicate = this.getPredicateFromHandle(handle);
            if (predicate === null) {
                throw "Couldnt find the predicate of id " + handle;
            }

            var canvasOffset = $(this.$el)
                .find(".work-zone")
                .offset();
            var x = e.clientX - canvasOffset.left + deltaX;
            var y = e.clientY - canvasOffset.top + deltaY;

            var meta = predicate.getmeta() || {};
            meta.inWorkZone = true;
            meta.coord = meta.coord || {};
            meta.coord.x = x;
            meta.coord.y = y;
            predicate.setmeta(meta);

            this.forceUpdate();
        },

        getSubgoals() { },

        getPredicates(subgoal) { },

        getExpressions(subgoal) { },

        // If we are in select mode, deselect all selected sub-expressions
        deselect() {
            if (this.selectMode) {
                this.resetSelection();
                this.forceUpdate();
            }
        },

        forceUpdate() {
            // UNORTHODOX: force a full re-render after metadata change
            this.renderIndex++;
            window.goal.renderIndex = this.renderIndex;

            //this.$forceUpdate();
        },

        onDragOverPredicate(e) {
            e.preventDefault();
        },

        get(ref) {
            let r = _.get(this.$refs, [ref, 0]);
            if (r) {
                return r;
            } else {
                // try to search into hypothesis zone
                let plist = this.get("plist");
                let r = _.get(plist.$refs, [ref, 0]);
                if (r) {
                    return r;
                } else {
                    return null;
                }
            }
        },

        getWorkZone() {
            return $(this.$el).find(".tab-pane.active .work-zone");
        },

        getHypothesisZone() {
            return $(this.$el).find(".hypothesis-zone");
        },

        fitHypsZone(btn) {
            //btn = $(btn.$el);
            //if (btn.hasClass("in-hypothesis-zone")) {
            //    let btnWidth = btn.outerWidth() + 80;
            //    if (btnWidth > this.hypsZoneWidth) {
            //        this.hypsZoneWidth = btnWidth;
            //    }
            //}
        },

        findElement(handle) {
            return $(this.$el).find(`[data-handle="${handle}"]`);
        },

        ready() {
            return new Promise(resolve => {
                $(this.$el).ready(resolve);
            });
        },

        enterSelectMode() {
            this.selectMode = true;
            $(".btn-select").addClass("active");
            //this.$forceUpdate();
        },

        exitSelectMode() {
            this.selectMode = false;
            $(".btn-select").removeClass("active");
            //this.$forceUpdate();
        },

        setDisplayMode(displayMode) {
            this.displayMode = displayMode;
        },

        resetSelection() {
            _.each(this.pathButtonMap, (button, path) => {
                if (button && button.removeAllSelectedPaths) {
                    button.removeAllSelectedPaths();
                }
            });
            this.pathButtonMap = {};
        },

        registerPath(path, button) {
            this.pathButtonMap[path] = button;
        },

        getButton(path) {
            return this.pathButtonMap[path];
        },

        QED() {
            this.qed = true;
        },

        addMenuIcon(faId) {
            if (!this.menuIcons.includes(faId)) {
                let icon = document.createElement("i");
                icon.id = faId;
                icon.classList.add("fa-solid");
                icon.classList.add("fa-" + faId);
                icon.classList.add("menu-icon");
                document.getElementById("menuIcons").appendChild(icon);
                this.menuIcons.push(faId);
            }
        },

        addActionItem(id, faId, title, action) {
            let item = {
                id: id,
                icon: '#' + faId,
                title: title,
                action: action
            };
            this.actionsMenu.items.push(item);
            this.addMenuIcon(faId);
        },

        populateActionsMenu() {
            let query = { kind: "ctxt", selection: this.getActiveSelection() };
            let actions = this.proofState.actions(query);

            let $this = this;
            actions.forEach((a, i) => {
                if (a.ui.kind == 'ctxt') {
                    console.log(a);
                    $this.addActionItem(i + 1, a.icon, a.description, a.action);
                }
            });
        },

        actionsMenuClicked(action) {
            this.sendActionCode(action.action);
        },

        openActionsMenu(e) {
            this.populateActionsMenu();
            this.actionsMenu.x = e.clientX - (this.actionsMenu.size / 2);
            this.actionsMenu.y = e.clientY - (this.actionsMenu.size / 2) - 135;
            this.$refs.actionsMenu.open();
        },

        actionsMenuClosed() {
            this.actionsMenu.items = [];
        }
    }
};
</script>

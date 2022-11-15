<style>
#proof-canvas {
    width: 100%;
    height: 100%;
    background-color: white;
    overflow: hidden;
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

/* .pi-btn.pi-predicate.dragged:after, .pi-btn.pi-expression.dragged:after  {
    content: "";
    position: absolute;
    top: 0;
    right: 0;
    width: 8px;
    height: 100%;
    background-color: black;
}

.pi-btn.pi-predicate.dragged:before, .pi-btn.pi-expression.dragged:before,
.pi-btn.pi-goal.dragged:before {
    content: "";
    position: absolute;
    top: 0;
    left: 0;
    width: 8px;
    height: 100%;
    background-color: black;
} */

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
    height: 100%;
    padding-left: 0px;
    position: relative;
    padding-left: 15px;
    padding-right: 15px;
}

.hypothesis-zone {
    position: static;
    padding-right: 0px;
    padding-left: 15px;
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

.work-zone {
    width: calc(75% - 5px);
}

.hypothesis-zone {
    width: 25%;
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
    <div id="proof-canvas" class="container-fluid" @click="unhighlight">
        <div class="row" style="height: 100%;">
            <div class="col" style="padding: 0;" :key="renderIndex">
                <template v-if="proofState">
                    <template v-if="proofState.closed()">
                        <fireworks></fireworks>
                    </template>

                    <template v-else>
                        <ul class="nav nav-tabs" id="subgoal-tab" role="tablist">
                            <li class="nav-item" v-for="(subgoal, i) in proofState.subgoals()" :key="subgoal.handle">
                                <a class="nav-link text-danger" :class="{ active: isActiveSubgoal(i) }" :id="getSubgoalId(subgoal) + '-tab'" data-toggle="tab" :href="'#' + getSubgoalId(subgoal)" role="tab" :aria-controls="getSubgoalId(subgoal)" aria-selected="true" :data-subgoal="i" v-html="getSubgoalString(subgoal)" @click="setTab(i)"></a>
                            </li>
                        </ul>
                        <div class="tab-content" id="subgoal-content">
                            <div v-for="(subgoal, i) in proofState.subgoals()" :key="subgoal.handle" class="tab-pane fade" :class="{show: isActiveSubgoal(i),active: isActiveSubgoal(i)}" :id="getSubgoalId(subgoal)" :aria-labelledby="getSubgoalId(subgoal) + '-tab'">
                                <div class="canvas row" style="height: 100%; position: relative;">
                                    <div class="hypothesis-zone" style=" width: 25%;" @click="deselect" :style="{ width: hypsZoneWidth + 'px', 'border-right': '1px solid rgba(0,0,0,0.1)', 'overflow-y': 'auto', 'height': 'calc(100vh - 120px)' }">
                                        <proposition-list :goal="subgoal" :context="subgoal.context()" :vars="subgoal.tvars()" :selectMode="selectMode" :displayMode="displayMode" ref="plist"></proposition-list>
                                    </div>
                                    <div class="dragbar"></div>
                                    <div class="work-zone" droppable="true" @drop="onDropPredicate" @dragover="onDragOverPredicate" @click="deselect" :style="{ width: workZoneWidth + 'px' }">
                                        <goal :subgoal="subgoal" :key="getGoalKey(i)" :selectMode="selectMode" :displayMode="displayMode" :ref="subgoal.handle"></goal>
                                        <predicate v-for="(predicate, j) in getPredicatesInWorkZone(subgoal)" :predicate="predicate" :selectMode="selectMode" :displayMode="displayMode" :key="getPredicateKey(i, j)" :ref="predicate.handle"></predicate>
                                        <expression v-for="expression in getExpressionsInWorkZone(subgoal)" :expression="expression" :selectMode="selectMode" :displayMode="displayMode" :key="expression.handle" draggable="true" :ref="expression.handle"></expression>
                                    </div>
                                </div>
                            </div>
                        </div>
                    </template>
                </template>
                <div class="alert alert-danger mx-auto prover-msg" :class="{ shown: errorMsg !== null }" role="alert">
                    {{ errorMsg }}
                </div>
                <div class="alert alert-warning mx-auto prover-msg" :class="{ shown: warningMsg !== null }" role="alert">
                    {{ warningMsg }}
                </div>
            </div>
        </div>
    </div>
</template>

<script>
import _ from "lodash";

import PropositionListVue from "./propositionList.vue";
import ExpressionVue from "./expression.vue";
import PredicateVue from "./predicate.vue";
import GoalVue from "./goal.vue";
import FireWorksVue from "./fireworks.vue";

export default {
    components: {
        "proposition-list": PropositionListVue,
        predicate: PredicateVue,
        expression: ExpressionVue,
        goal: GoalVue,
        fireworks: FireWorksVue
    },
    data: function() {
        return {
            proofState: null,
            errorMsg: null,
            warningMsg: null,

            hypsZoneWidth_: 0,
            docWidth: null,

            renderIndex: 0,

            selectMode: false, // true if we are selecting a subpath, false otherwise
            displayMode: "html", // "html" or "mathml"

            selection: {}
        };
    },
    computed: {
        hypsZoneWidth: {
            get: function () {
                return this.hypsZoneWidth_;
            },
            set: function (newWidth) {
                let hypsWidths = $(".pi-btn.in-hypothesis-zone")
                    .map(function () { return $(this).outerWidth(); })
                    .toArray();
                let maxHypWidth = _.max(hypsWidths) + 80;
                if (hypsWidths.length === 0 || newWidth >= maxHypWidth) {
                    this.hypsZoneWidth_ = newWidth;
                }
            }
        },
        workZoneWidth: {
            get: function () {
                return this.docWidth - this.hypsZoneWidth - 5;
            }
        },
    },
    created: function() {
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
    updated: function() {
        /*
            if( this.proofState !== null && this.proofState !== undefined ) {
                // re-render mathjax after this component is mounted
                MathJax.Hub.Queue(["Typeset",MathJax.Hub]);
            }
            */

        if( this.displayMode == "mathml" ) {
            if( this.proofState !== null && this.proofState !== undefined ) {
                // MathJax.Hub.Queue(["Typeset",MathJax.Hub]);
            }
        }

        this.bindDragBar();
    },

    mounted: function() {
        // set a resize watcher
        this.handleResize();
        window.addEventListener("resize", this.handleResize);
        this.hypsZoneWidth = 0.25 * this.docWidth;
    },

    beforeDestroy: function() {
        window.removeEventListener("resize", this.handleResize);
    },

    methods: {
        bindDragBar: function() {
            let self = this;

            // Resize horizontally
            var dragBar = $(this.$el).find(".dragbar");
            dragBar.off("mousedown");
            dragBar.on("mousedown", function(e) {
                e.preventDefault();
                $(document).mouseup(function(e) {
                    $(document).unbind("mousemove");
                });
                $(document).mousemove(function(e) {
                    // debounce the new size affectation so we won't parse the whole proof too often
                    _.debounce(() => {
                        self.hypsZoneWidth = e.pageX;
                    }, 20)();
                });
            });

            // same as before but for touch interfaces
            dragBar.off("touchstart");
            dragBar.on("touchstart", function(e) {
                e.preventDefault();
                $(document).on("touchend", function(e) {
                    $(document).unbind("touchmove");
                });
                $(document).on("touchmove", function(e) {
                    let pageX = _.get(e, ["changedTouches", 0, "pageX"]);
                    let pageY = _.get(e, ["changedTouches", 0, "pageY"]);
                    if( pageX && pageY ) {
                        // debounce the new size affectation so we won't parse the whole proof too often
                        _.debounce(() => {
                            self.hypsZoneWidth = pageX;
                        }, 20)();
                    }
                });
            });
        },

        setGoal(proof) {
            this.$set(this, "proofState", proof);
            this.addToHistory(proof);
        },

        getGoalKey(index) {
            return "proof-" + this.proofState.handle + "-goal-" + "-" + index;
        },

        getPredicateKey(sg, p, i, j) {
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

        redo() {
            if (this.historyIndex < this.history.length - 1) {
                this.historyIndex++;
                window.goal = this.proofState = this.history[this.historyIndex];
                this.$forceUpdate();
                this.resetSelection();
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

        sendAction(actionCode) {
            try {
                let actionb = window.goal.getactionb();
                let subgoalIndex = this.getActiveSubgoal();
                window.ipcRenderer.send('action', actionb, subgoalIndex);
            } catch (e) {
                this.$refs.proofCanvas.showErrorMessage(e);
                window.ipcRenderer.send('error', this.$refs.proofCanvas.errorMsg);
            }
        },

        generalize(predicate) {
            let subgoal = predicate.parent;

            try {
                var proof = subgoal.generalize(predicate.handle);
                this.resetSelection();
                this.setProofState(proof);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        applyCutHypothesis(subgoal, text) {
            try {
                var proof = subgoal.cut(text);
                this.resetSelection();
                this.setProofState(proof);
            } catch (e) {
                this.showErrorMessage(e);
            }
        },

        applyAddLemma(subgoal, name) {
            try {
                var proof = subgoal.addlemma(name);
                this.resetSelection();
                this.setProofState(proof);
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

        moveHyp(subgoal, fromHandle, toHandle) {
            var proof = subgoal.move(fromHandle, toHandle);
            this.setProofState(proof);
        },

        setProofState(proofState) {
            try {
                // set the current active tab since the prover doesn't transmit root metadata on apply()
                proofState.setmeta({ activeSubgoal: this.getActiveSubgoal() });
                window.goal = this.proofState = proofState;
                this.addToHistory(this.proofState);
                this.resetSelection();
                this.$forceUpdate();
            } catch (e) {
                this.showErrorMessage("Failed to apply new proof state");
            }
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
            return _.filter(subgoal.tvars(), o => {
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
            var handle = parseInt(e.dataTransfer.getData("handle"));
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

        getSubgoals() {},

        getPredicates(subgoal) {},

        getExpressions(subgoal) {},

        // If we are in select mode, deselect all selected sub-expressions
        deselect() {
            if (this.selectMode) {
                _.each(this.$refs["plist"], sublist => {
                    _.each(sublist.$refs, arr => {
                        _.each(arr, button => {
                            if (button && button.removeAllSelectedPaths) {
                                button.removeAllSelectedPaths();
                            }
                        });
                    });
                });

                _.each(this.$refs, arr => {
                    _.each(arr, button => {
                        if (button && button.removeAllSelectedPaths) {
                            button.removeAllSelectedPaths();
                        }
                    });
                });

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
            btn = $(btn.$el);
            if (btn.hasClass("in-hypothesis-zone")) {
                let btnWidth = btn.outerWidth() + 80;
                if (btnWidth > this.hypsZoneWidth) {
                    this.hypsZoneWidth = btnWidth;
                }
            }
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
                button.removeAllSelectedPaths();
            });
            this.pathButtonMap = {};
        },

        registerPath(path, button) {
            this.pathButtonMap[path] = button;
        },

        getButton(path) {
            return this.pathButtonMap[path];
        }
    }
};
</script>
